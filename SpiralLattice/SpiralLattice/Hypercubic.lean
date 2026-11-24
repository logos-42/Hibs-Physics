/-
SpiralLattice.Hypercubic — the string theorem on the d-dimensional hypercubic lattice.

  HC1 ★★★ (string theorem)  On ℤ^d, take any finite set of unit links carrying integer flux,
          with charge +1 at x, −1 at y and no other charge.  Then
                energy ≥ |x − y|₁   (Manhattan distance).
          At strong coupling the potential between two opposite divergences therefore grows at
          least linearly with distance: V(R) ≥ (g²/2a)·R.  A straight unit string attains it.

Proof idea: each of the |x − y|₁ half-spaces lying between x and y emits exactly one unit of
flux (Gauss, GL2), and a unit link crosses the boundary of at most one of them (cut bound ST2).
-/
import SpiralLattice.StringTheorem

namespace SpiralLattice

/-- Decidable equality of lattice sites `Fin d → Int` (core Lean has no such instance). -/
instance siteDecEq (d : Nat) : DecidableEq (Fin d → Int) := fun f g =>
  if h : ∀ i ∈ List.finRange d, f i = g i then
    isTrue (funext fun i => h i (List.mem_finRange i))
  else
    isFalse (fun e => h (fun i _ => by rw [e]))

/-- Move one step in the positive direction along axis `j`. -/
def shift {d : Nat} (a : Fin d → Int) (j : Fin d) : Fin d → Int :=
  fun i => if i = j then a i + 1 else a i

/-- Consecutive integers lo, lo+1, …, lo+n−1. -/
def intRange (lo : Int) : Nat → List Int
  | 0 => []
  | n + 1 => lo :: intRange (lo + 1) n

theorem mem_intRange {lo t : Int} {n : Nat} (h : t ∈ intRange lo n) : lo ≤ t ∧ t < lo + n := by
  induction n generalizing lo with
  | zero => simp [intRange] at h
  | succ n ih =>
    simp only [intRange, List.mem_cons] at h
    rcases h with h | h
    · omega
    · have := ih h; omega

theorem intRange_length (lo : Int) (n : Nat) : (intRange lo n).length = n := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih => simp [intRange, ih]

theorem filter_length_mono {α : Type} (q r : α → Bool) (H : ∀ x, q x = true → r x = true)
    (L : List α) : (L.filter q).length ≤ (L.filter r).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases hq : q a <;> by_cases hr : r a <;> simp [hq, hr] <;>
      first | omega | (have := H a hq; simp_all)

theorem intRange_filter_eq (lo t : Int) (n : Nat) :
    ((intRange lo n).filter (fun s => decide (s = t))).length ≤ 1 := by
  induction n generalizing lo with
  | zero => simp [intRange]
  | succ n ih =>
    simp only [intRange, List.filter_cons]
    by_cases h : lo = t
    · subst h
      have : (intRange (lo + 1) n).filter (fun s => decide (s = lo)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro s hs
        have := mem_intRange hs
        simp; omega
      simp [this]
    · simp [h]; exact ih (lo + 1)

/-- A half-space cut: `{z | z axis ≤ level}` if `up`, else `{z | level < z axis}`. -/
structure Cut (d : Nat) where
  axis : Fin d
  level : Int
  up : Bool

def Cut.region {d : Nat} (C : Cut d) : (Fin d → Int) → Bool :=
  fun z => if C.up then decide (z C.axis ≤ C.level) else decide (C.level < z C.axis)

/-- The half-space cuts perpendicular to axis `i` lying between coordinates `a` (source) and
`b` (sink), oriented so that each contains the source. -/
def axisCuts {d : Nat} (i : Fin d) (a b : Int) : List (Cut d) :=
  if a ≤ b then (intRange a (b - a).toNat).map (fun t => ⟨i, t, true⟩)
  else (intRange b (a - b).toNat).map (fun t => ⟨i, t, false⟩)

def cutsBetween {d : Nat} (x y : Fin d → Int) : List (Cut d) :=
  (List.finRange d).flatMap (fun i => axisCuts i (x i) (y i))

/-- Manhattan distance on ℤ^d. -/
def manhattan {d : Nat} (x y : Fin d → Int) : Int :=
  sumL (fun i => ((x i - y i).natAbs : Int)) (List.finRange d)

theorem axisCuts_length {d : Nat} (i : Fin d) (a b : Int) :
    ((axisCuts i a b).length : Int) = ((a - b).natAbs : Int) := by
  unfold axisCuts
  by_cases h : a ≤ b
  · simp [h, intRange_length]; omega
  · simp [h, intRange_length]; omega

theorem cutsBetween_length {d : Nat} (x y : Fin d → Int) :
    ((cutsBetween x y).length : Int) = manhattan x y := by
  unfold cutsBetween manhattan
  rw [List.length_flatMap]
  generalize List.finRange d = L
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons, sumL_cons]
    push_cast
    rw [← ih, axisCuts_length]

theorem mem_axisCuts {d : Nat} {i : Fin d} {a b : Int} {C : Cut d} (h : C ∈ axisCuts i a b) :
    C.axis = i ∧
      ((C.up = true ∧ a ≤ C.level ∧ C.level < b) ∨ (C.up = false ∧ b ≤ C.level ∧ C.level < a)) := by
  unfold axisCuts at h
  by_cases hab : a ≤ b
  · simp only [hab, ite_true, List.mem_map] at h
    obtain ⟨t, ht, rfl⟩ := h
    have h1 := mem_intRange ht
    have h2 : ((b - a).toNat : Int) = b - a := Int.toNat_of_nonneg (by omega)
    exact ⟨rfl, Or.inl ⟨rfl, show a ≤ t by omega, show t < b by omega⟩⟩
  · simp only [hab, ite_false, List.mem_map] at h
    obtain ⟨t, ht, rfl⟩ := h
    have h1 := mem_intRange ht
    have h2 : ((a - b).toNat : Int) = a - b := Int.toNat_of_nonneg (by omega)
    exact ⟨rfl, Or.inr ⟨rfl, show b ≤ t by omega, show t < a by omega⟩⟩

/-- Every cut between `x` and `y` contains `x` and not `y`. -/
theorem cut_separates {d : Nat} {x y : Fin d → Int} {C : Cut d} (h : C ∈ cutsBetween x y) :
    C.region x = true ∧ C.region y = false := by
  unfold cutsBetween at h
  rw [List.mem_flatMap] at h
  obtain ⟨i, _, hi⟩ := h
  obtain ⟨hax, hcase⟩ := mem_axisCuts hi
  subst hax
  rcases hcase with ⟨hu, h1, h2⟩ | ⟨hu, h1, h2⟩
  · simp [Cut.region, hu]; omega
  · simp [Cut.region, hu]; omega

/-- A unit link along axis `j` crosses a cut only if the cut is perpendicular to `j` at the
link's starting coordinate. -/
theorem crosses_cut {d : Nat} {C : Cut d} {a : Fin d → Int} {j : Fin d} {f : Int}
    (h : crosses C.region ⟨a, shift a j, f⟩ = true) : C.axis = j ∧ C.level = a j := by
  unfold crosses Cut.region shift at h
  by_cases hj : C.axis = j
  · subst hj
    refine ⟨rfl, ?_⟩
    by_cases hu : C.up <;> simp [hu] at h <;> omega
  · simp [hj] at h

theorem cuts_disjoint {d : Nat} (x y : Fin d → Int) (a : Fin d → Int) (j : Fin d) (f : Int) :
    ((cutsBetween x y).filter (fun C => crosses C.region ⟨a, shift a j, f⟩)).length ≤ 1 := by
  unfold cutsBetween
  rw [List.filter_flatMap, List.length_flatMap]
  have hterm : ∀ i ∈ List.finRange d,
      (((axisCuts i (x i) (y i)).filter (fun C => crosses C.region ⟨a, shift a j, f⟩)).length : Int)
        ≤ (if j = i then 1 else 0) := by
    intro i _
    by_cases hij : j = i
    · subst hij
      simp only [ite_true]
      unfold axisCuts
      by_cases hxy : x j ≤ y j
      · simp only [hxy, ite_true, List.filter_map, List.length_map]
        have hm := filter_length_mono
          ((fun C => crosses C.region ⟨a, shift a j, f⟩) ∘ (fun t => (⟨j, t, true⟩ : Cut d)))
          (fun s => decide (s = a j))
          (fun s hs => by
            have := crosses_cut (C := ⟨j, s, true⟩) (a := a) (j := j) (f := f) hs
            simpa using this.2) (intRange (x j) (y j - x j).toNat)
        have := intRange_filter_eq (x j) (a j) (y j - x j).toNat
        have : ((List.filter ((fun C => crosses C.region ⟨a, shift a j, f⟩) ∘
            (fun t => (⟨j, t, true⟩ : Cut d))) (intRange (x j) (y j - x j).toNat)).length) ≤ 1 := by omega
        exact_mod_cast this
      · simp only [hxy, ite_false, List.filter_map, List.length_map]
        have hm := filter_length_mono
          ((fun C => crosses C.region ⟨a, shift a j, f⟩) ∘ (fun t => (⟨j, t, false⟩ : Cut d)))
          (fun s => decide (s = a j))
          (fun s hs => by
            have := crosses_cut (C := ⟨j, s, false⟩) (a := a) (j := j) (f := f) hs
            simpa using this.2) (intRange (y j) (x j - y j).toNat)
        have := intRange_filter_eq (y j) (a j) (x j - y j).toNat
        have : ((List.filter ((fun C => crosses C.region ⟨a, shift a j, f⟩) ∘
            (fun t => (⟨j, t, false⟩ : Cut d))) (intRange (y j) (x j - y j).toNat)).length) ≤ 1 := by omega
        exact_mod_cast this
    · simp only [hij, ite_false]
      have : (axisCuts i (x i) (y i)).filter (fun C => crosses C.region ⟨a, shift a j, f⟩) = [] := by
        rw [List.filter_eq_nil_iff]
        intro C hC hcr
        have h1 := (mem_axisCuts hC).1
        have h2 := (crosses_cut hcr).1
        exact hij (h2.symm.trans h1)
      simp [this]
  have hsum : ((((List.finRange d).map (fun i =>
      ((axisCuts i (x i) (y i)).filter (fun C => crosses C.region ⟨a, shift a j, f⟩)).length)).sum : Nat) : Int)
      = sumL (fun i => (((axisCuts i (x i) (y i)).filter
          (fun C => crosses C.region ⟨a, shift a j, f⟩)).length : Int)) (List.finRange d) := by
    generalize List.finRange d = L
    induction L with
    | nil => simp
    | cons i L ih => simp only [List.map_cons, List.sum_cons, sumL_cons]; push_cast; rw [ih]
  have h1 := sumL_le hterm
  rw [sumL_ite_eq _ _ (List.nodup_finRange d)] at h1
  have h2 : (if j ∈ List.finRange d then (1 : Int) else 0) = 1 := by simp [List.mem_finRange]
  rw [h2] at h1
  have : ((((List.finRange d).map (fun i =>
      ((axisCuts i (x i) (y i)).filter (fun C => crosses C.region ⟨a, shift a j, f⟩)).length)).sum : Nat) : Int) ≤ 1 := by
    rw [hsum]; exact h1
  exact_mod_cast this

/-- HC1 ★★★ String theorem on ℤ^d. -/
theorem string_theorem {d : Nat} (c : List (Link (Fin d → Int))) (vs : List (Fin d → Int))
    (hc : Covers vs c)
    (hstep : ∀ l ∈ c, ∃ j, l.head = shift l.tail j)
    (x y : Fin d → Int) (hx : x ∈ vs) (hy : y ∈ vs)
    (hρ : ∀ z ∈ vs, div c z = (if x = z then 1 else 0) - (if y = z then 1 else 0)) :
    manhattan x y ≤ energy c := by
  rw [← cutsBetween_length]
  have hlen : ((cutsBetween x y).map Cut.region).length = (cutsBetween x y).length := by simp
  rw [← hlen]
  apply cut_bound_energy
  · intro S hS
    rw [List.mem_map] at hS
    obtain ⟨C, hC, rfl⟩ := hS
    obtain ⟨h1, h2⟩ := cut_separates hC
    exact netOut_eq_one c vs hc x y hx hy hρ C.region h1 h2
  · intro l hl
    obtain ⟨j, hj⟩ := hstep l hl
    have hl' : l = ⟨l.tail, shift l.tail j, l.flux⟩ := by
      cases l; simp_all
    rw [List.filter_map, List.length_map]
    have := cuts_disjoint x y l.tail j l.flux
    rw [hl'] at this ⊢
    simpa [Function.comp_def] using this

end SpiralLattice

namespace SpiralLattice

/-! ### HC2: the bound is attained by a straight string (example R = 3 on ℤ²). -/

def pt (a b : Int) : Fin 2 → Int := fun i => if i = 0 then a else b

def straightString : List (Link (Fin 2 → Int)) :=
  [⟨pt 0 0, pt 1 0, 1⟩, ⟨pt 1 0, pt 2 0, 1⟩, ⟨pt 2 0, pt 3 0, 1⟩]

def stringSites : List (Fin 2 → Int) := [pt 0 0, pt 1 0, pt 2 0, pt 3 0]

theorem straightString_gauss : ∀ z ∈ stringSites, div straightString z =
    (if pt 0 0 = z then 1 else 0) - (if pt 3 0 = z then 1 else 0) := by decide

theorem straightString_energy : energy straightString = 3 := by decide

theorem straightString_manhattan : manhattan (pt 0 0) (pt 3 0) = 3 := by decide

/-- HC2: equality in the string theorem is attained (energy = Manhattan distance = 3). -/
theorem string_attained : energy straightString = manhattan (pt 0 0) (pt 3 0) := by
  rw [straightString_energy, straightString_manhattan]

end SpiralLattice
