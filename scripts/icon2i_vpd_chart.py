#!/usr/bin/env python3
import argparse
import json
import math
from datetime import datetime
from pathlib import Path

import matplotlib.pyplot as plt

A = 17.625
B = 243.04
SKIN_TEMP_C = 33.0


def is_number(v):
    return isinstance(v, (int, float)) and not isinstance(v, bool) and math.isfinite(v)


def saturation_vapor_pressure(t_c):
    return 0.61094 * math.exp(A * t_c / (t_c + B))


def dew_point_from_t_rh(t_c, rh):
    if not (is_number(t_c) and is_number(rh)) or rh <= 0:
        return None
    gamma = math.log(rh / 100.0) + A * t_c / (B + t_c)
    return B * gamma / (A - gamma)


def normalize_json(src_path, out_path, city):
    with open(src_path, encoding="utf-8") as f:
        data = json.load(f)

    hourly = data.setdefault("hourly", {})
    direct = hourly.get("dew_point_2m") or []
    temps = hourly.get("temperature_2m") or []
    rhs = hourly.get("relative_humidity_2m") or []
    times = hourly.get("time") or []
    n = max(len(times), len(direct), len(temps), len(rhs))

    dew = []
    used_fallback = False
    for i in range(n):
        direct_v = direct[i] if i < len(direct) else None
        if is_number(direct_v):
            dew.append(float(direct_v))
            continue
        t = temps[i] if i < len(temps) else None
        rh = rhs[i] if i < len(rhs) else None
        calc = dew_point_from_t_rh(t, rh)
        if calc is not None:
            dew.append(round(calc, 2))
            used_fallback = True
        else:
            dew.append(None)

    hourly["dew_point_2m"] = dew
    data.setdefault("hourly_units", {})["dew_point_2m"] = "°C"
    data["city"] = city
    data["dew_point_2m_source"] = "direct_or_calculated_from_temperature_2m_and_relative_humidity_2m"

    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)

    return data, used_fallback


def series_for_date(data, target_date):
    """Return LOCAL clock hours exactly as supplied by Open-Meteo Europe/Rome JSON."""
    times = data.get("hourly", {}).get("time") or []
    dew = data.get("hourly", {}).get("dew_point_2m") or []
    result_hours, result_vpd = [], []
    skin_es = saturation_vapor_pressure(SKIN_TEMP_C)

    for t_str, td in zip(times, dew):
        if not is_number(td):
            continue
        # Open-Meteo already returned timezone=Europe/Rome. These strings are local wall-clock
        # times, so DO NOT pass them through Matplotlib date/timezone conversion.
        dt_local = datetime.fromisoformat(t_str)
        if dt_local.date() != target_date:
            continue
        result_hours.append(dt_local.hour + dt_local.minute / 60.0)
        result_vpd.append(skin_es - saturation_vapor_pressure(float(td)))
    return result_hours, result_vpd


def italian_date_label(d):
    months = ["gennaio", "febbraio", "marzo", "aprile", "maggio", "giugno", "luglio", "agosto", "settembre", "ottobre", "novembre", "dicembre"]
    return f"{d.day} {months[d.month - 1]} {d.year}"


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--salerno-raw", required=True)
    p.add_argument("--milano-raw", required=True)
    p.add_argument("--salerno-json", required=True)
    p.add_argument("--milano-json", required=True)
    p.add_argument("--run-iso", required=True, help="Example: 2026-08-19T00:00Z")
    p.add_argument("--forecast-date", required=True, help="Local Europe/Rome date, YYYY-MM-DD")
    p.add_argument("--output", required=True)
    p.add_argument("--summary", required=True)
    args = p.parse_args()

    # Defensive stale-file removal: never leave a previous graph at the requested output path.
    output_path = Path(args.output)
    output_path.unlink(missing_ok=True)
    Path(args.summary).unlink(missing_ok=True)

    salerno, s_fallback = normalize_json(args.salerno_raw, args.salerno_json, "Salerno")
    milano, m_fallback = normalize_json(args.milano_raw, args.milano_json, "Milano")

    run_dt = datetime.fromisoformat(args.run_iso.replace("Z", "+00:00"))
    target_date = datetime.strptime(args.forecast_date, "%Y-%m-%d").date()

    s_hours, s_vpd = series_for_date(salerno, target_date)
    m_hours, m_vpd = series_for_date(milano, target_date)

    # A current-day run can legitimately cover fewer than 24 local hours.
    # Example: a 00 UTC run in CEST starts at 02:00 local. Do not reject it for that reason.
    if not s_hours or not m_hours:
        Path(args.summary).write_text(
            "ready=false\n"
            f"run={args.run_iso}\n"
            f"forecast_date={target_date.isoformat()}\n"
            f"salerno_valid_hours={len(s_hours)}\n"
            f"milano_valid_hours={len(m_hours)}\n",
            encoding="utf-8",
        )
        return 3

    fig, ax = plt.subplots(figsize=(16, 9))

    ax.axhspan(0.0, 1.5, facecolor="#e9c2c2", alpha=0.85, label="Afa pesante (0–1.5)")
    ax.axhspan(1.5, 2.0, facecolor="#efd2a8", alpha=0.85, label="Afoso (1.5–2.0)")
    ax.axhspan(2.0, 2.5, facecolor="#f4e5a8", alpha=0.85, label="Leggermente afoso (2.0–2.5)")
    ax.axhspan(2.5, 4.0, facecolor="#c9dfc8", alpha=0.90, label="Niente afa (>2.5)")

    ax.plot(s_hours, s_vpd, color="#1f77b4", marker="o", linewidth=2.2, markersize=6, label="Salerno")
    ax.plot(m_hours, m_vpd, color="#ff7f0e", marker="o", linewidth=2.2, markersize=6, label="Milano")

    run_label = run_dt.strftime("%d/%m/%Y %H UTC")
    forecast_label = italian_date_label(target_date)
    ax.set_title(
        f"Disagio da afa — confronto città, previsione per oggi {forecast_label}\n"
        f"Ultimo run ICON-2I disponibile: {run_label} | Pelle umida assunta: 33 °C",
        fontsize=20,
        fontweight="bold",
    )
    ax.set_ylabel("VPD pelle–aria (kPa)", fontsize=13)
    ax.set_xlabel("Ora locale (Europe/Rome)", fontsize=13)
    ax.set_ylim(0, 4.0)
    ax.set_xlim(0, 23)
    ticks = list(range(0, 24, 2))
    ax.set_xticks(ticks)
    ax.set_xticklabels([f"{h:02d}:00" for h in ticks], rotation=45, ha="right")
    ax.grid(True, alpha=0.18)

    handles, labels = ax.get_legend_handles_labels()
    order_names = [
        "Salerno", "Milano", "Afa pesante (0–1.5)", "Afoso (1.5–2.0)",
        "Leggermente afoso (2.0–2.5)", "Niente afa (>2.5)"
    ]
    order = [labels.index(name) for name in order_names]
    ax.legend([handles[i] for i in order], [labels[i] for i in order], loc="upper right", ncol=2, framealpha=0.95, fontsize=11)

    fig.text(
        0.025,
        0.035,
        "Fonte dati: Open-Meteo Single Runs API | Modello: ItaliaMeteo ARPAE ICON-2I | "
        f"Run usato: {run_label} | Variabile usata: dew_point_2m",
        fontsize=10,
    )
    fig.tight_layout(rect=[0.02, 0.07, 0.99, 0.98])
    fig.savefig(output_path, dpi=170, bbox_inches="tight")
    plt.close(fig)

    with output_path.open("rb") as f:
        if f.read(8) != b"\x89PNG\r\n\x1a\n":
            output_path.unlink(missing_ok=True)
            return 4

    def extrema(name, vals):
        return f"{name}_min_kpa={min(vals):.2f}\n{name}_max_kpa={max(vals):.2f}\n"

    Path(args.summary).write_text(
        "ready=true\n"
        f"run={args.run_iso}\n"
        f"forecast_date={target_date.isoformat()}\n"
        f"salerno_valid_hours={len(s_hours)}\n"
        f"milano_valid_hours={len(m_hours)}\n"
        f"salerno_first_local_hour={s_hours[0]:05.2f}\n"
        f"salerno_last_local_hour={s_hours[-1]:05.2f}\n"
        f"milano_first_local_hour={m_hours[0]:05.2f}\n"
        f"milano_last_local_hour={m_hours[-1]:05.2f}\n"
        f"salerno_dew_point_source={'fallback' if s_fallback else 'direct'}\n"
        f"milano_dew_point_source={'fallback' if m_fallback else 'direct'}\n"
        + extrema("salerno", s_vpd)
        + extrema("milano", m_vpd),
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
