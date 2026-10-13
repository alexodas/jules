# Audit critico delle ipotesi del teorema di Pitagora da isotropia

**Data:** 13 ottobre 2026  
**Stato:** analisi matematica indipendente dalla compilazione Lean; gli esempi sotto NON sono ancora formalizzati nel kernel Lean.  
**Scopo:** valutare se il teorema formalizzato sia tautologico, implicitamente circolare, o una caratterizzazione condizionale della geometria euclidea.

## 1. Oggetto esatto dell'audit

Fonte primaria: [PythagoreanIsotropy.lean, release v0.1.0](https://github.com/alexodas/pythagorean-isotropy-lean/blob/v0.1.0/PythagoreanIsotropy.lean), teorema **PythagoreanIsotropy.pythagoras_from_metric_free_quarter_turn**; vedere anche [AXIOMS.md](https://github.com/alexodas/pythagorean-isotropy-lean/blob/v0.1.0/AXIOMS.md).

La conclusione è $T: a^2+b^2=c^2$. Le ipotesi nominate sono otto:

1. **hAction:** la famiglia lineare $F:\mathbb R\to\mathrm{End}(\mathbb R^2)$ soddisfa $F_{s+t}=F_sF_t$.
2. **hQ:** $Q(1,0)=(0,1)$ e $Q^2=-I$.
3. **hMember:** esiste $\theta$ con $F_\theta=Q$.
4. **hAxis:** $L(z,0)=|z|$.
5. **hMirror:** $L(x,-y)=L(x,y)$.
6. **hRigid:** $L(F_t(x,y))=L(x,y)$ per ogni $t,x,y$.
7. **hToAxis:** per il vettore specifico $(a,b)$ esistono $t,z$ con $z\geq0$ e $F_t(a,b)=(z,0)$.
8. **hc:** $L(a,b)=c$.

**Precisazione:** $L$ è formalmente una qualunque funzione $\mathbb R^2\to\mathbb R$. Le ipotesi **non** la dichiarano una norma; non assumono continuità, disuguaglianza triangolare, positività definita, né omogeneità. Anche $F$ non è assunto continuo.

## 2. La catena realmente dimostrata

- Da **hQ + linearità**: $Q(x,y)=(-y,x)$.
- Da **hAction + hMember**: ciascun $F_t$ commuta con $Q$; quindi
  $F_t(x,y)=(u_tx-v_ty,v_tx+u_ty)$.
- Da **hRigid + hMirror + hAxis**:
  $L(u_t,v_t)=L(u_t,-v_t)=1$ e
  $F_t(u_t,-v_t)=(u_t^2+v_t^2,0)$.
  Pertanto $u_t^2+v_t^2=1$, **senza** usare la formula della lunghezza euclidea.
- Da **hToAxis**: $F_t(a,b)=(z,0)$; l'algebra dà
  $a^2+b^2=z^2$.
- Da **hRigid + hAxis + hc**, siccome $z\geq0$, segue
  $c=L(a,b)=L(z,0)=z$ e dunque $a^2+b^2=c^2$.

**Verdetto formale:** non è una mera riscrittura letterale della tesi. È una deduzione condizionale che fa emergere la forma euclidea da ipotesi di simmetria e congruenza. **Verdetto fondazionale:** resta da giustificare quelle ipotesi senza utilizzare a monte la stessa metrica euclidea.

## 3. Controesempi controllabili: che cosa succede se togliamo un'ipotesi

Le seguenti costruzioni sono **contro-modelli matematici descritti sulla carta**, non certificati in Lean. Servono a mostrare che l'esclusione di una premessa può consentire una conclusione falsa.

### A. Senza hMember: geometria ellittica (controesempio elementare)

Sia $S(x,y)=(x,2y)$ e sia $R_t$ la rotazione ordinaria di angolo $t$ nel piano. Definiamo

$$L(x,y)=\sqrt{x^2+4y^2},\qquad F_t=S^{-1}R_t S.$$

In coordinate:

$$F_t(x,y)=\bigl(x\cos t-2y\sin t,\ \tfrac12 x\sin t+y\cos t\bigr).$$

- hAction: $F_{s+t}=F_sF_t$ (coniugazione del gruppo delle rotazioni).
- hAxis: $L(z,0)=|z|$.
- hMirror: $L(x,-y)=L(x,y)$.
- hRigid: $L(F_t(x,y))=L(x,y)$; l'identità algebrica è
  $(x\cos t-2y\sin t)^2+4(\tfrac12x\sin t+y\cos t)^2=x^2+4y^2$.
- hQ: il **Q standard** $Q(x,y)=(-y,x)$ soddisfa hQ.
- hToAxis: scegliendo $(a,b)=(0,1)$ e $t=-\pi/2$, otteniamo $F_t(0,1)=(2,0)$.
- hc: $c=L(0,1)=2$.

Eppure $a^2+b^2=1$ e $c^2=4$: **T è falsa**. La premessa mancante è proprio **hMember**: nessun $F_t$ coincide con il quarto di giro standard $Q$, poiché la seconda coordinata di $F_t(1,0)$ è al massimo $1/2$, mentre quella di $Q(1,0)$ è $1$.

**Interpretazione:** la compatibilità *effettiva* del moto con il quarto di giro calibrato esclude la geometria ellittica anisotropa.

### B. Senza hQ: stesso modello ellittico (controesempio elementare)

Manteniamo $L,F,a,b,c$ del caso A. Poniamo però $Q=I$. Allora **hMember** è vera ($F_0=I=Q$), ma **hQ** è falsa. Tutte le altre ipotesi sono vere; $1\ne4$.

### C. Senza hRigid (controesempio elementare)

Siano $F_t=R_t$, $Q=R_{\pi/2}$, e $L(x,y)=|x|$.
hAction, hQ, hMember, hAxis e hMirror sono vere.
Con $(a,b)=(0,1)$, $t=-\pi/2$, abbiamo $F_t(0,1)=(1,0)$: hToAxis è vera.
Pongo $c=L(0,1)=0$, quindi hc è vera.
La tesi richiederebbe $1=0$, falso.
**Manca hRigid**, perché le rotazioni ordinarie non conservano $|x|$.

### D. Senza hAxis (controesempio elementare)

Siano $F_t=R_t$, $Q=R_{\pi/2}$, $L(x,y)=0$ per tutti $x,y$.
Prendiamo $(a,b)=(1,0)$ e $c=0$.
Tutte le altre ipotesi sono vere (per hToAxis scegliamo $t=0,z=1$), ma $1\ne0$.
Manca la calibrazione hAxis.

### E. Senza hc (controesempio elementare)

Siano $F_t=R_t$, $Q=R_{\pi/2}$, $L(x,y)=\sqrt{x^2+y^2}$, $(a,b)=(1,0)$; scegliamo arbitrariamente $c=0$.
Tutte le altre ipotesi sono vere; hc è falsa e anche $1=0$ è falso.
**Nota:** hc serve a identificare la lettera $c$ con la lunghezza; è una premessa di denominazione, non una proprietà sostanziale della geometria.

## 4. Controesempi più sofisticati: assenza di regolarità

Le altre tre ipotesi richiedono, per i controesempi qui proposti, funzioni molto non regolari. È importante non spacciarle per modelli geometrici ordinari. Si può rendere ciascuna costruzione rigorosa utilizzando basi di Hamel; **non è stata formalizzata in Lean**.

### F. Senza hMirror: flusso che dilata in modo discontinuo

Scegliamo una funzione additiva $\alpha:\mathbb R\to\mathbb R$ tale che
$\alpha(\pi/2)=0$ e $\alpha(1)=\log 2$. Esiste mediante una base di Hamel poiché $1$ e $\pi/2$ sono linearmente indipendenti su $\mathbb Q$.

Identifichiamo il piano con i complessi e definiamo
$F_t(re^{i\varphi})=e^{\alpha(t)}r\,e^{i(\varphi+t)}$,
$L(re^{i\varphi})=r e^{-\alpha(\varphi)}$ per $r>0$, e $L(0)=0$.
La definizione di $L$ è indipendente dalla scelta dell'argomento perché $\alpha(2\pi)=0$.

hAction, hQ con $Q(z)=iz$, hMember ($F_{\pi/2}=Q$), hAxis e hRigid sono vere.
Per il punto $(a,b)=(\cos1,\sin1)$, scegliamo $t=-1$:
$F_{-1}(a,b)=(1/2,0)$, perciò hToAxis è vera, e $c=L(a,b)=1/2$ soddisfa hc.
Ma $a^2+b^2=1\ne1/4=c^2$.
**Manca hMirror**: $L(\cos1,\sin1)=1/2$, mentre $L(\cos1,-\sin1)=2$.

La costruzione evidenzia perché, **senza alcuna continuità richiesta**, la simmetria speculare elimina dilatazioni patologiche.

### G. Senza hToAxis: sottogruppo denso ma non transitivo

Sia $q:\mathbb R\to\mathbb Q$ un omomorfismo additivo non nullo e suriettivo con $q(1)=1$ (si ottiene usando una base di Hamel).
Definiamo $F_t=R_{\pi q(t)/2}$, $Q=R_{\pi/2}$.
Per $z\ne0$ di modulo $r$ e argomento $\varphi$, poniamo:
$L(z)=r$ se $\varphi/\pi\in\mathbb Q$ modulo $2$;
$L(z)=2r$ altrimenti. Pongo $L(0)=0$.

hAction, hQ, hMember, hAxis, hMirror e hRigid sono vere.
Prendiamo $(a,b)=(\cos(\pi\sqrt2),\sin(\pi\sqrt2))$ e $c=L(a,b)=2$.
Il vettore ha modulo euclideo $1$; tuttavia l'orbita sotto $F$ aggiunge soltanto multipli razionali di $\pi$, quindi **non** raggiunge un asse. hToAxis è falsa e $1\ne4$.

### H. Senza hAction: isometrie individuali non legate da un'azione

Definiamo una funzione primitiva non regolare $L$ come segue:
- $L(0,0)=0$;
- se $(x,y)=r(m,n)$ con $m,n$ interi coprimi e $r\ne0$, poniamo $L(x,y)=|r|$ (il valore è ben definito);
- sulle direzioni con pendenza irrazionale poniamo $L(x,y)=0$.

Questa funzione è invariante per le matrici intere unimodulari, compresi $Q(x,y)=(-y,x)$, il riflesso $(x,y)\mapsto(x,-y)$ e $M(x,y)=(x,y-x)$.
Definiamo $F_1=Q$, $F_2=M$, $F_t=I$ per ogni altro $t$.
hQ, hMember, hAxis, hMirror e hRigid sono vere; prendendo $(a,b)=(1,1)$, otteniamo $F_2(1,1)=(1,0)$, quindi hToAxis. Inoltre $c=L(1,1)=1$, perciò hc.
Ma $a^2+b^2=2\ne1=c^2$.
**Manca hAction**, ad esempio $F_2\ne F_1F_1$.

## 5. Che cosa insegnano i controesempi

1. Gli esempi A–E sono semplici e spiegano con chiarezza il ruolo di hMember, hQ, hRigid, hAxis, hc.
2. Gli esempi F–H mostrano come la **mancanza di ipotesi di continuità e di normatività di L** renda importanti hMirror, hToAxis e hAction; richiedono ancora verifica indipendente dettagliata e formalizzazione.
3. Gli esempi propongono *test di essenzialità per la conclusione*, non una certificazione Lean di indipendenza delle ipotesi e soprattutto non una prova della loro priorità filosofica.
4. Anche se ogni premessa fosse necessaria nel sistema dichiarato, **la questione della circolarità esplicativa rimarrebbe**: da dove provengono i principi di rigidità e raggiungibilità? Si possono giustificare senza prima utilizzare la metrica euclidea?

## 6. La questione centrale: «contiene la tesi» non equivale a «la implica»

Dal punto di vista della logica, se le ipotesi $H$ dimostrano $T$, allora $H$ **implica** $T$: questo è ciò che deve accadere in qualunque dimostrazione.

Possiamo parlare di **premessa mascherata** quando $H$ coincide con $T$, è una semplice riformulazione di $T$, o la sua giustificazione presuppone già $T$.
Parliamo invece di **caratterizzazione strutturale** quando $H$ è un sistema autonomo di principi con contenuto indipendentemente motivato e da esso emerge $T$ per deduzione.

Nel nostro caso hRigid, hMember e hToAxis **in combinazione** incorporano forti vincoli sulla geometria euclidea. È scorretto descrivere la verifica Lean come una dimostrazione di quei vincoli da premesse geometriche elementari. Altrettanto scorretto sarebbe chiamare l'implicazione formalizzata *non valida*: la sua correttezza condizionale resta.

Se esigiamo che la derivazione costituisca una fondazione indipendente di Pitagora, occorre formalizzare o argomentare a parte l'esistenza e la rigidità della famiglia di trasformazioni da principi più primitivi.

## 7. Conseguenze per la pubblicazione

**Non emerge qui una confutazione del teorema formale della release v0.1.0.** Il suo enunciato condizionale è coerente con l'audit. È tuttavia ragionevole descriverlo come **caratterizzazione/derivazione assiomatica condizionata della norma euclidea basata su simmetrie di gruppo**.

Non affermare sulla sola base della compilazione Lean:
- dimostrazione senza presupposti geometrici sostanziali;
- assiomi minimi e indipendenti;
- esistenza del flusso ottenuta da sola incidenza/congruenza;
- novità storica dimostrata.

Il README e AXIOMS.md della pubblicazione già contengono buona parte di queste cautele; **non suggerisco correzioni urgenti della release** sulla base di questo audit preliminare.

## 8. Prossimo esperimento Lean consigliato

Nel laboratorio privato Jules, formalizzare anzitutto il **controesempio ellittico A** come teorema Lean che prova sette premesse e la negazione della conclusione dopo aver rimosso hMember. Questo sarebbe più informativo del solo esempio tautologico T ⇒ T.

In seconda battuta formalizzare i controesempi elementari C, D, E. La compilazione di un singolo lemma artificiosamente circolare rimane un utile esperimento didattico separato.

**Stato al 13/10/2026:** documento di audit analitico. Nessuno dei contro-modelli descritti in questo documento è qui presentato come verificato da Lean o da GitHub Actions.