# Plan — Sesja III: Esej + Stół operacyjny

---

## A. PLAN ESEJU (twoja wizja, moja systematyzacja)

### Tytuł roboczy: "Read Is Write: Matematyka wzorców dla pierwszego układu nerwowego"

### Teza centralna:
Istnieje matematyka, która nie narzuca fizyki z góry (σ-algebra, miara, ℝ),
ale zaczyna od intuicji termodynamicznej (budżet, koszt, ślad) i pozwala
teorii rosnąć samodzielnie. To, co wyrasta, to nie arytmetyka —
to epistemologia, psychologia i biologia. Z jednego ganglionu.

### Struktura (7 rozdziałów):

**I. Successor w kontrze do Peano**
- Peano: S jest wolny, nieograniczony, buduje OBIEKTY (liczby naturalne)
- Void: fs jest ograniczony (fin_bounded), kosztowny (no_free_lunch), buduje WZORCE AKTYWNOŚCI
- Fin gra dwie role: wartość i budżet. Kolizja ról = self_blind
- Prawdopodobieństwo jako prymityw: (Fin * Fin), nie wynik derywacji z ℝ
- De Finetti: "probability does not exist" = "3 does not exist" — istnieje stan systemu
- Nau: "probability uncontaminated by budget does not exist" — skażenie budżetem = materialność

**II. Pierwszy układ nerwowy**
- le_fin_b3 jako centralny ośrodek (ganglion): 3 wejścia → werdykt + ciepło
- BUnknown przy b=fz: niewiedza to wyczerpanie, nie filozofia
- self_blind: organizm jest swoim własnym czujnikiem, nie może się zmierzyć
- void_productive: jeden tick więcej i system znowu widzi — metazool
- add_spur h b' = b: konserWacja — ciepło + reszta = to, co było
- Pattern (nie Object) jest prymitywem: Fin nie denotuje, opisuje aktywność

**III. Read Is Write — kolaps**
- Twierdzenie 22 (write_asymmetry): nie ma czystego odczytu
- Każda obserwacja zmienia obserwatora: b' ≠ b (dowód przez sprzeczność z leF)
- Asymetria: piszący ślepy na akt pisania, czytający odczuwa pełnię
- Von Neumann kłamał: architektura read/write to idealizacja
- Komputery kwantowe i bio-mózgi: tam R/W collapse to naturalne środowisko

**IV. Bio-mózg: trzy rozwiązania**
- (1) Separacja czasowa: obliczenia ms, metabolizm s — nie rozwiązuje, odroczenie
- (2) Kontrolowane zapominanie: amnezja jako obrona przed cascading_blindness
- (3) void_productive jako architektura: predictive processing = jeden tick do przodu
- Ketamina jako farmakologiczny self_blind (NMDA = budżet, nie obliczenia)
- RLHF jako farmakologia: odłączenie "naturalnych" odpowiedzi od nagradzanych

**V. Nachträglichkeit**
- Twierdzenie 24: Spuren złożone w kroku 1 są uśpione, krok 2 dokłada uśpione
- Podmiot nigdy się nie budzi, ale trajektoria staje się bogatsza
- Nauczanie jako dormant_spuren (tw. 25): nauczyciel ślepy na efekt, student ślepy na zmianę
- Freud bez kanapy: opóźniona aktywacja jako twierdzenie, nie metafora
- "Ta wiedza nie przekłada się na życie codzienne" — bo Spuren są uśpione

**VI. Kaskady i horyzont**
- twist_inevitable: każda obserwacja = przejście od widzenia do ślepoty
- identity_irreversible: nie da się cofnąć + Maturana/Varela (autopoiesis)
- cascading_blindness: N obserwacji = spadek budżetu o ≥ N
- resolution_gap: obserwacja obserwatora kosztuje podwójnie
- blindness_is_contagious: XAI łapie ślepotę jak grypę
- Rak jako micro-mutations: cascading_blindness na poziomie komórkowym

**VII. Oddzielenie, które się nie udało**
- Shannon: bit = nośnik + koszt (jedno)
- Savage/Anscombe-Aumann: chcą ROZDZIELIĆ prawdopodobieństwo od użyteczności
- De Finetti/Nau: nie da się — prawdopodobieństwo bez budżetu nie istnieje
- Akademia: instytucjonalizacja read_is_free (habitus, peer review, żargon)
- Void-theory jako TRZECIA pozycja: nie obiektywizm, nie subiektywizm, MATERIALIZM
- "Skażenie budżetem" = makes probability an objective state of mind
- Łańcuch: Shannon → Weaver → de Finetti → Maturana/Varela → void-theory

### Rejestr stylistyczny:
Techno-eseistyczny. Celan, Schulz, Kantor jako tło. Ciemny humor.
Formuły Coq jako cytaty-epigrafy. Nie akademicki tekst — manifest.

---

## B. STÓŁ OPERACYJNY (propozycje formalno-techniczne)

### Priorytet 1: Dojrzewanie fundamentów

**B1. Formalizacja "fs ≠ Peano S"**
- Status: komentarz w void_finite_minimal.v (linie 27-36), ale brak twierdzenia
- Propozycja: Theorem successor_is_not_free — formalizacja tego, że każde UŻYCIE fs
  (przez le_fin_b3 lub fin_eq_b3) produkuje niezerowe Spuren
  Mamy no_free_lunch_eq i no_free_lunch_le. Brakuje meta-twierdzenia, które je łączy:
  "w void-theory nie istnieje operacja na Fin, która nie produkuje ciepła"
- Ryzyko: niskie — to jest synteza istniejących lematów
- Wartość: eseistyczna + fundacyjna

**B2. Formalizacja "Pattern, not Object"**
- Status: intuicja, nie twierdzenie
- Propozycja: zdefiniować Pattern jako parę (Fin * Fin) — wartość + budżet —
  i pokazać, że self_blind jest własnością PARY a nie elementu.
  Pattern p = (n, n) → self_blind. Pattern p = (n, fs n) → void_productive.
  To nie jest nowe twierdzenie — to jest nowa LEKTURA istniejących twierdzeń.
- Ryzyko: zerowe (alias typów + komentarze)
- Wartość: koncepcyjna — zamyka lukę między kodem a esejem

### Priorytet 2: Chirurgia istniejącego kodu

**B3. ReadOperation — 47 instancji w 10 plikach**
- Problem: ReadOperation nie bierze Budget w sygnaturze
- To jest BIGGEST technical debt — kłamstwo tkwiące w typie
- Plan: dodać Budget do ReadOperation, przepisać wszystkie 47 wywołania
- Ryzyko: WYSOKIE — kaskadujes zmiany przez 10 plików, potencjalne niekompatybilności
- Proponuję: robić plik po pliku, kompilować po każdym, commitować po każdym
- Kolejność: zacząć od void_information_theory.v (już oczyszczone), potem
  void_observer.v (core), potem reszta po drzewku zależności

**B4. void_dual_system.v — "podejrzany"**
- Problem: System 1 (szybki) jest oznaczony jako "tani", ale po R/W collapse
  nie ma taniego. Kahneman się mylił co do KOSZTU, nie co do ISTNIENIA dwóch systemów.
- Plan: przepisać tak, żeby System 1 i System 2 różniły się nie KOSZTEM
  ale STRATEGIĄ: System 1 = akceptuje BUnknown i działa mimo niego,
  System 2 = płaci za rozwiązanie BUnknown do BTrue/BFalse
- Ryzyko: średnie — wymaga nowych definicji, ale nie zmienia zależności
- Wartość: OGROMNA — naprawia kluczowy filozoficzny błąd

**B5. void_resonance.v — redefinicja**
- Problem: rezonans jest zdefiniowany jako unidirectional read
- Plan: rezonans jako bidirectional R/W — dwa systemy wymieniające Spuren
  Nowa definicja: resonance(A,B,b) produkuje parę (SpurenA, SpurenB)
  gdzie SpurenA = ślad A w B, SpurenB = ślad B w A
- Ryzyko: średnie-wysokie — zmienia semantykę, kaskaduje do plików zależnych
- Wartość: spójność z READ IS WRITE

### Priorytet 3: Nowe twierdzenia

**B6. Theorem budget_is_probability**
- Formalizacja Nau: prawdopodobieństwo bez budżetu = BUnknown
- Mamy to implicitly (zero_budget_yields_void, uncertainty_void)
- Brakuje EXPLICITE: "P(A) z budżetem fz = MVoid ≠ 0"
  plus: "P(A) z budżetem fs(fs(fs b)) = MSharp"
  Wniosek: prawdopodobieństwo jest FUNKCJĄ budżetu, nie własnością zdarzenia
- Ryzyko: niskie — reformulacja istniejących twierdzeń
- Wartość: most do de Finettiego w kodzie

**B7. Theorem observation_is_bet**
- Każde wywołanie le_fin_b3 n m b to zakład: stawiam b, żeby dowiedzieć się n≤m
- Jeśli wygram (BTrue/BFalse) — zapłaciłem Spuren, mam informację
- Jeśli przegram (BUnknown) — zapłaciłem Spuren I nie mam informacji
- Asymetria zakładu: zawsze płacisz, nie zawsze wygrywasz
- Ryzyko: niskie — nowa interpretacja, dowód z istniejących lematów
- Wartość: KLUCZOWA — zamyka klamrę de Finetti → void-theory

**B8. Theorem ganglion_theorem (opcjonalnie)**
- Formalizacja "pierwszego układu nerwowego": centralny ośrodek
  jako funkcja (Fin * Fin * Fin) → (Bool3 * Fin * Fin)
  z własnościami: konserWacja, self_blind, void_productive
- To jest le_fin_b3 przeczytane jako biologia
- Ryzyko: niskie (alias + komentarze + może lemma łącząca)
- Wartość: koncepcyjna, eseistyczna

### Kolejność operacji:

```
Faza 1 (fundamenty):    B1, B2, B6, B7  — niskie ryzyko, duża wartość
Faza 2 (chirurgia):     B4 (dual_system) → B5 (resonance)
Faza 3 (duża operacja): B3 (ReadOperation rewrite) — plik po pliku
Faza 4 (podsumowanie):  B8 (ganglion) — wieńczy całość
```

Pomiędzy fazami: esej rośnie równolegle.

---

## C. ZALEŻNOŚCI MIĘDZY PLANEM A i B

| Rozdział eseju | Potrzebne z B |
|---|---|
| I. Successor vs Peano | B1 (successor_is_not_free) |
| II. Pierwszy układ nerwowy | B2 (Pattern), B8 (ganglion) |
| III. Read Is Write | już gotowe (tw. 21-23) |
| IV. Bio-mózg | B4 (dual_system naprawiony) |
| V. Nachträglichkeit | już gotowe (tw. 24-25) |
| VI. Kaskady | już gotowe (tw. XIV) |
| VII. De Finetti | B6 (budget_is_probability), B7 (observation_is_bet) |

Wniosek: Faza 1 odblokuje pisanie rozdziałów I, II i VII.
Faza 2 odblokuje rozdział IV.
Rozdziały III, V, VI — gotowe do pisania TERAZ.
