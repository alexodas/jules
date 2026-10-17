# Jules Spectral Geometry

**Programma di ricerca matematica sperimentale in Lean 4 e Mathlib.**

## 1. Intendimento generale: dalla geometria dei tasselli agli zeri di una funzione analitica

Vogliamo studiare come una tassellazione, anche **aperiodica** e priva di righe e colonne naturali, possa determinare uno spettro tramite un operatore geometrico. Distinguiamo ciò che **scegliamo per definire il modello** da ciò che **emerge come autovalore**.

A ogni tassello `t` associamo un'energia individuale `V(t)`, che potrà dipendere da un numero arbitrario di proprietà: baricentro, area, forma, orientamento, chiralità quando pertinente, gerarchia di sostituzione e altre caratteristiche geometriche. A ogni coppia di tasselli associamo un peso d'interazione `w(t,u)`, anche quando non sono adiacenti. Per interazioni simmetriche e non negative, il modello di partenza sarà:

```math
(H\psi)(t)=\underbrace{V(t)\psi(t)}_{\text{energia individuale}}+\underbrace{\sum_{u\ne t}w(t,u)(\psi(t)-\psi(u))}_{\text{interazioni}}.
```

Il nostro obiettivo è dimostrare dapprima proprietà molto generali di questi operatori; in seguito studieremo tassellazioni particolari, come Penrose, Ammann–Beenker, Pinwheel e Spectre. **Non sceglieremo direttamente gli autovalori**: vorremmo ricavarli dall'operatore completo. L'energia individuale e la legge delle interazioni sono dati del modello, non autovalori già fissati.

Su una porzione finita di `N` tasselli, un operatore reale simmetrico ammette `N` autovalori reali contando le molteplicità. Su infiniti tasselli potrebbero invece comparire parti continue dello spettro. Studieremo condizioni adeguate, come autoaggiuntezza, positività e risolvente compatto, che permettano di enumerare gli autovalori:

```math
0<\lambda_0\le\lambda_1\le\lambda_2\le\cdots,\qquad \lambda_n\longrightarrow+\infty.
```

### Il risultato analitico acquisito

Disponiamo già della **definizione e formalizzazione Lean** della funzione canonica

```math
D_q(s)=\prod_{n=0}^{\infty}\left(1-\frac{(s-c)^2}{d^2q_n^2}\right),\qquad d\ne0.
```

La definizione, il criterio di convergenza e i teoremi sulla localizzazione degli zeri si trovano nel file **[`SpectralGeometry/CanonicalProduct.lean`](SpectralGeometry/CanonicalProduct.lean)**. In particolare, se `q_n>0` e

```math
\sum_{n=0}^{\infty}\frac1{q_n^2}<\infty,
```

i teoremi formalizzati garantiscono la convergenza appropriata del prodotto, che **tutti i suoi zeri giacciono sulla retta prescelta** `s=c+dt` con `t` reale, e che ogni livello `q_n` produce zeri in `s=c\pm d q_n`.

Il nuovo problema è ottenere questi livelli come **autovalori dell'operatore geometrico infinito**:

```math
H\psi_n=\lambda_n\psi_n,\qquad q_n=\lambda_n.
```

Dovremo dimostrare che l'operatore scelto possiede uno spettro discreto positivo enumerabile, e inoltre che

```math
\sum_{n=0}^{\infty}\frac1{\lambda_n^2}<\infty.
```

Solo allora potremo definire rigorosamente `D_H(s)=D_{\lambda}(s)`. Per `c=1/2` e `d=i` avremo zeri in

```math
s=\frac12\pm i\lambda_n.
```

**La retta è imposta dalla costruzione del prodotto, non ricavata da una proprietà della zeta di Riemann.** Non abbiamo ancora formalizzato l'operatore infinito o il suo legame spettrale con il prodotto; saranno oggetto dei prossimi risultati. Questo progetto non dimostra l'ipotesi di Riemann e non identifica `D_q` con la zeta.

### Compilazione e verifica

Il nucleo analitico è definito in `SpectralGeometry/CanonicalProduct.lean`; `SpectralGeometry.lean` ne è il punto di ingresso. La toolchain è Lean 4 `v4.35.0` con Mathlib della stessa versione.

```bash
lake update
lake exe cache get
lake build
```

La verifica automatica di GitHub Actions controlla la compilazione su ogni modifica a `main` e su ogni pull request.
