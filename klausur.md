---
title: Zusammenfassung AUD für Klausur
author: Per Göttlicher
date: 02.09.2023
disable-header-and-footer: true
listings-no-page-break: true
table-use-row-colors: true
header-includes:
- |
  ```{=latex}
  \usepackage{awesomebox}
  ```
pandoc-latex-environment:
  noteblock: [note]
  tipblock: [tip]
  warningblock: [warning]
  cautionblock: [caution]
  importantblock: [important]
---

# Basisbegriffe

## Bestimmt

- Determiniertheit: Algorithmus liefert bei gleicher Eingabe gleiche Ausgabe
- Determinismus: Algorithmus durchläuft für gleiche Eingabe immer die gleichen Schritte/Zustände

## Anwendbar

- Allgemeinheit: Algorithmus für ganze Problemklasse anwendbar
- Korrektheit: Falls Algorithmus terminiert, ist die Ausgabe richtig

## Berechenbar

- Terminierung: Algorithmus stoppt in endlicher Zeit
- Finitheit: Algorithmus hat endliche Beschreibung
- Effektivität: Schritte sind auf einer Maschine ausführbar

## Datenstruktur

Eine Datenstruktur ist eine Methode, Daten für den Zugriff und die Modifikation zu organisieren

## Algorithmus

Eine aus endlich vielen Schritten bestehende,
ausführbare Handlungsvorschrift zur eindeutigen Umwandlung von Eingabe- in Ausgabedaten

\pagebreak

# Sortieralgorithmen

## Insertion Sort

- aufsteigend

  ```pseudo
  insertionSort(A)
      FOR i=1 TO A.length-1 DO
          // insert A[i] in pre-sorted sequence A[0..i-1]
          key=A[i];
          j=i-1; // search for insertion point backwards
          WHILE j>=0 AND A[j]>key DO
              A[j+1]=A[j]; // move elements to right
              j=j-1;
          A[j+1]=key;
  ```

- absteigend

  ```pseudo
  insertionSort(A)
      FOR i=1 TO A.length-1 DO
          // insert A[i] in pre-sorted sequence A[0..i-1]
          key=A[i];
          j=i-1; // search for insertion point backwards
          WHILE j>=0 AND A[j]<key DO
              A[j+1]=A[j]; // move elements to right
              j=j-1;
          A[j+1]=key;
  ```

## Bubblesort

```pseudo
bubbleSort(A)
    FOR i = A.length - 1 DOWNTO 0 DO
        FOR j = 0 TO i - 1 DO
            IF A[j] > A[j+1] THEN SWAP(A[j], A[j+1]);
                //temp=A[j+1]; A[j+1]=A[j]; A[j]=temp;
```

unsortiert: [2,4,1,3]

sortiert: [1,2,3,4]

## Stonesort

```pseudo
stoneSort(A)
    FOR i = A.length - 1 DOWNTO 0 DO
        FOR j = A.length - 1 TO A.length - 1 DO
            IF A[j] < A[j-1] THEN SWAP(A[j], A[j-1]);
                //temp=A[j-1]; A[j-1]=A[j]; A[j]=temp;
```

unsortiert: [2,4,1,3]

sortiert: [4,3,2,1]

## Merge Sort

```pseudo
mergeSort(A,l,r) // initial call: l=0,r=A.length-1
    IF l<r THEN //more than one element
        m=floor((l+r)/2); // m (rounded down) middle (last index left part)
        mergeSort(A,l,m); // sort left part
        mergeSort(A,m+1,r); // sort right part
        merge(A,l,m,r); // merge into one
```

::: tip
Idee:

Liste in Hälften teilen, diese rekursiv sortieren und wieder zusammen sortieren.
:::

```pseudo
merge(A,l,m,r) // requires l<=m<=r
    //array B with r-l+1 elements as temporary storage
    pl=l; pr=m+1; // position left, right
    FOR i=0 TO r-l DO // merge all elements
        IF pr>r OR (pl=<m AND A[pl]=<A[pr]) THEN
            B[i]=A[pl];
            pl=pl+1;
        ELSE //next element at pr
            B[i]=A[pr];
            pr=pr+1;
    FOR i=0 TO r-l DO
        A[i+l]=B[i]; //copy back to A
```

::: tip
Idee:

Nächstes Element kleinstes Element aus linker oder rechter Teilliste und dann in dieser Liste eine Position nach vorne gehen.

Jede Teilliste wird genau einmal durchlaufen $\Rightarrow$ Laufzeit von `merge` $= \Theta(n_L+n_R)$
:::

## Quicksort

```pseudo
quicksort(A,l,r) // initial call: l=0,r=A.length-1
    IF l<r THEN //more than one element
        p=partition(A,l,r); // p partition index
        quicksort(A,l,p); // sort left part
        quicksort(A,p+1,r); // sort right part
```

::: tip
Idee:

Divide & Conquer wie bei Merge Sort.

Liste partitionieren, dann Teillisten rekursiv sortieren.
:::

```pseudo
partition(A,l,r) //requires l<r, returns int in l..r-1
    pivot=A[l];
    pl=l-1; pr=r+1; //move from left resp. right
    WHILE pl<pr DO
        REPEAT pl=pl+1 UNTIL A[pl]>=pivot; //move left up
        REPEAT pr=pr-1 UNTIL A[pr]=<pivot; //move right down
        IF pl<pr THEN
            Swap(A[pl],A[pr]);
        p=pr; //store current value
    return p // A[l..p] left, A[p+1..r] right
```

::: tip
Idee:

Ein Element (z.B. erstes) als Pivot wählen und Elemente partitionieren, sodass $Elemente \leq Pivot$ in der linken Teilliste sind und $Elemente \geq Pivot$ in der rechten Teilliste

Laufzeit von `partition` $\Theta(n)$
:::

::: note
Randomisirte Variante von Quicksort:

Wählt als Pivot Element immer zufällig eines der Elemente und tauscht es an den Anfang der Liste, damit der gleiche Algorithmus verwendet werden kann.
:::

## Laufzeiten

+---------------------------------------+-----------------------------+-------------------------------------------+
| Inserion Sort                         | Merge Sort                  | Quicksort                                 |
+=======================================+=============================+===========================================+
| Laufzeit $\Theta(n^2)$                | Beste asymptotische         | Worst-Case-Laufzeit $\Theta(n^2)$\        |
|                                       | Laufzeit $\Theta(n\log(n))$ | randomisirt mit erwarteter                |
|                                       |                             | Laufzeit $\Theta(n \cdot log(n))$         |
+---------------------------------------+-----------------------------+-------------------------------------------+
| einfache Implementierung              |                             | in Praxis meist schneller als Merge Sort, |
|                                       |                             | da weniger Kopieroperationen              |
+---------------------------------------+-----------------------------+-------------------------------------------+
| für kleine $n \leq 50$ oft beste Wahl |                             | Implementierungen schalten für kleine $n$ |
|                                       |                             | meist auf Insertion Sort                  |
+---------------------------------------+-----------------------------+-------------------------------------------+

::: note
Untere Schranke für vergleichsbasierte Sortieralgorithmen:

$\Omega(n \cdot \log(n)) \Rightarrow$ jeder vergleichsbasierter Algorithmus muss mindestens $n \cdot \log(n)$ Schritte machen.
:::

# Konzepte

## Divide & Conquer (& Combine)

Problem in Teilprobleme zerlegen und Teilprobleme rekursiv lösen.

### Beispiele

- Mergesort
  - Liste in Hälften Teilen, rekursiv sortieren, wieder zusammen sortieren
- Quicksort

# Landau Symbole / asymptotische Komplexität

## O-Notation

$$
O(g) = \{f: \exists c \in \mathbb{R}_{>0},n_0 \in \mathbb{N},\forall n \geq n_0, 0 \leq f(n) \leq c g(n) \}
$$

$f$ wächst höchstens so schnell wie $g$

::: note
$O(n) \subseteq O(n^2) \subseteq O(n^3) \subseteq O(n^4) \subseteq O(n^5) \subseteq \dots$
:::

## O-Notation Rechenregeln

Konstanten: $f(n)=a$ mit $a \in \mathbb{R}_{>0}$ konstant. Dann $f(n)=O(1)$

Skalare Multiplikation: $f=O(g)$ und $a \in \mathbb{R}_{>0}$. Dann $a \cdot f = O(g)$

Addition: $f_1=O(g_1)$ und $f_2=O(g_2)$. Dann $f_1+f_2=O(max\{g_1,g_2\})$ ($max$ punktweise)

Multiplikation: $f_1=O(g_1)$ und $f_2=O(g_2)$. Dann $f_1 \cdot f_2=O(g_1 \cdot g_2)$

## $\Omega$-Notation

$$\Omega(g) = \{f: \exists c \in \mathbb{R}_{>0},n_0 \in \mathbb{N},\forall n \geq n_0, 0 \leq c g(n) \leq f(n) \}$$

$f$ wächst mindestens so schnell wie $g$

::: note
$\Omega(n) \supseteq \Omega(n^2) \supseteq \Omega(n^3) \supseteq \Omega(n^4) \supseteq \Omega(n^5) \supseteq \dots$
:::

## Zusammenhang O, $\Omega$ und $\Theta$

Für beliebige $f(n) , g(n): \mathbb{N} \mathbb{R} \rightarrow \mathbb{R}_{>0}$ gilt:

$f(n) = \Theta(g(n))$ genau dann,wenn $f(n) = O(gn(n))$ und $f(n) = \Omega(g(n))$

::: important
**Hinweis**

$f = O(g)$ übliche Schreibweise, sollte als $f \in O(g)$ gelesen werden

Ungleichungen mit $\leq$ nur mir O

Ungleichungen mit $\geq$ nur mit $\Omega$

Wenn $=$, dann $\Theta$
:::

## Komplexitätklassen

| Klasse                    | Bezeichnung   | Beispiel               |
| ------------------------- | ------------- | ---------------------- |
| $\Theta(1)$               | Konstant      | Einzeloperation        |
| $\Theta(\log(n))$         | Logarithmisch | Binäre Suche           |
| $\Theta(n)$               | Linear        | Squentielle Suche      |
| $\Theta(n \cdot \log(n))$ | Quasilinear   | Sortieren eines Arrays |
| $\Theta(n^2)$             | Quadratisch   | Matrixaddition         |
| $\Theta(n^3)$             | Kubisch       | Matrixmultiplikation   |
| $\Theta(n^k)$             | Polynomell    |                        |
| $\Theta(2^n)$             | Expotentiell  | Travelling-Salesmen    |
| $\Theta(n!)$              | Faktoriell    | Permutation            |

\pagebreak

# Rekursionsgleichungen/Laufzeitanalyse

(am Beispiel Merge Sort)

Sei $T(n)$ die maximale Anzahl von Schritten für Arrays der Größe $n$ (für $n \geq 2$):

$$
T(n) \leq 2 \cdot T(n/2) + c + d \cdot n
$$

$2 \cdot T(n/2)$: 2 rekursive Aufrufe für jeweils halb so großes Array

$c$: IF + floor (konstanter Aufwand)

$d \cdot n$:Merge (Aufwand $O(n)$)

$T(1) \leq c$ da l=r

::: tip
Es gilt auch $T(n) \geq \Omega(n \cdot \log(n))$

Somit ist die Laufzeit von Merge Sort $\Theta(n \cdot \log(n))$
:::

## Manuelle Iteration

$$
T(n) \leq 2 \cdot T(n/2) + c \cdot n
$$
$$
T(n) \leq 2 \cdot (2 \cdot T(n/4) + (c\cdot n)/2) + c \cdot n
$$
$$
\vdots
$$
$$
T(n) \leq 2 \cdot (2 \cdot (2 \cdots (2 \cdot T(1) + 2) \cdots + (c\cdot n)/4) + (c\cdot n)/2) + c \cdot n
$$
$$
T(n) \leq 2 \cdot (2 \cdot (2 \cdots (2 \cdot c + 2) \cdots + (c\cdot n)/4) + (c\cdot n)/2) + c \cdot n
$$
$2 \cdot (2 \cdot (2 \cdots (2 \cdot \rightarrow$ $\log_2(n)$-mal
$$
T(n) \leq 2^{\log_2(n)} \cdot c + \log_2(n) \cdot c \cdot n = O(n \cdot \log(n))
$$

## Mastertheorem

Allgemeine Form der Rekursionsgleichung:

$$
T(n) = a \cdot T(n/b) + f(n), \qquad T(1) = \Theta(1)
$$

mit $a \geq 1, b > 1$ und $f(n)$ eine asymptotische Funktion

### Definition

Seien $a \geq 1$ und $b > 1$ Konstanten. Sei $f(n)$ eine positive Funktion und $T(n)$ über den nicht-negativen ganzen Zahlen durch die Rekursionsgleichung
$$
T(n) = a \cdot T(n/b) + f(n), \qquad T(1) = \Theta(1)
$$

definiert, wobei wir $n/b$ so interpretieren, dass damit entweder $\lfloor n/b \rfloor$ oder $\lceil n/b \rceil$ gemeint ist. Dann besitzt $T(n)$ die folgenden asymptotischen Schranken:

1. Gilt $f(n) = O(n^{\log_b(a)-\epsilon})$ für eine Konstante $\epsilon > 0$, dann $T(n) = \Theta(n^{\log_b(a)})$
2. Gilt $f(n) = \Theta(n^{\log_b(a)})$, dann gilt $T(n) = \Theta(n^{\log_b(a)} \cdot \log_2(n))$
3. Gilt $f(n) = \Omega(n^{\log_b(a)+\epsilon})$ für eine Konstante $\epsilon > 0$ und $a \cdot f(n/b) \leq c \cdot f(n)$ für eine Konstante $c < 1$ und hinreichend große $n$, dann ist $T(n) = \Theta(f(n))$

::: note
Entscheidend ist das Verhältnis von $f(n)$ zu $n^{\log_b(a)}$

1. Wenn $f(n)$ polynomiell kleiner als $n^{\log_b(a)}$, dann $T(n) = \Theta(n^{\log_b(a)})$
2. Wenn $f(n)$ und $n^{log_b(a)}$ gleiche Größenordnung, dann $T(n) = \Theta(n^{\log_b(a)}\cdot \log(n))$
3. Wenn $f(n)$ polynomiell größer als $n^{log_b(a)}$ und $a \cdot f(n/b) \leq c \cdot f(n)$, dann $T(n) = \Theta(f(n))$

Bei 1. & 3. unterscheidet sich der polynomielle Faktgor $n^\epsilon$
:::

### Beispiele

1. Merge Sort:

   $$
   T(n) = 2 \cdot T(n/2) + c \cdot n
   $$

   Fall 2, da $a = b = 2; \log_b(a)=1; f(n) = \Theta(n)=\Theta(n^{\log_b(a)})$

   $$
   T(n) = \Theta(n^{\log_b(a)}\cdot \log_2(n))=\Theta(n \cdot \log_2(n))
   $$

2. $T(n) = 4 \cdot T(n/3) + c \cdot n$

   Fall 1, da $a=4; b= 3; \log_b(a) = 1.26 \dots; \epsilon = 0.26\dots; f(n) = \Theta(n)=\Theta(n^{\log_b(a)-\epsilon})$

   $T(n)=\Theta(n^{\log_b(a)})=\Theta(n^{1.26 \dots})$

3. $T(n) = 3 \cdot T(n/3) + c \cdot n^2$

   Fall 3, da $a=b=3; \log_b(a)=1; \epsilon = 1; f(n) = \Theta(n^2)=\Theta(n^{\log_b(a)+\epsilon}); 3 \cdot f(n) = (c \cdot n^2)/3 \leq \frac{1}{3} \cdot f(n)$

   $T(n)=\Theta(f(n))=\Theta(n^2)$

4. $T(n) = 25 \cdot T(n/5) + n^4 \cdot \log_3(n) +15$

   Fall 3, da $a=25; b= 5; \log_b(a)=2; \epsilon = 1; f(n) = n^4 \cdot \log_3(n) + 15 = \Omega(n^{2+\epsilon}) = \Omega(n^3); 25 \cdot f(n/5) = 25 \cdot \frac{n^4}{5^4} \cdot \log_3(\frac{n}{5})+15 \leq \frac{1}{25} \cdot f(n)$

   $T(n) = \Theta(f(n)) = \Theta(n^4 \cdot \log(n))$

5. $T(n) = 4 \cdot T(n/5) + n^2 \cdot \log(n)$

   Fall 3, da $a=b=4; \log_b(a)=1; \epsilon = 0.1; f(n) = n^2 \cdot \log(n)=\Omega(n^2) \subseteq \Omega(n^{1+\epsilon}); 4 \cdot f(n) = \frac{n^2}{4} \cdot \log(\frac{n}{4}) \leq \frac{1}{4} \cdot f(n)$

   $T(n)=\Theta(f(n))=\Theta(n^2 \cdot \log(n))$

6. $T(n) = 8 \cdot T(n/2) + n^3 \cdot \log_4(n+16)$

   Kein Fall anwendbar, da $a = 8; b = 2; \log_b(a)=3; f(n) = n^3 \cdot \log_4(n+16)$ für jedes $\epsilon > 0$ gilt $f(n) \neq O(n^{\log_b(a) - \epsilon})$, $f(n) \neq \Omega(n^{\log_b(a) + \epsilon})$ und $f(n) \neq \Theta(n^{\log_b(a)})$