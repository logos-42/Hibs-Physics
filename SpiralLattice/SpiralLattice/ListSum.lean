/-
SpiralLattice.ListSum — finite sums over lists (Lean 4 core only, no Mathlib).

These are bookkeeping lemmas used by the lattice theorems. Nothing physical here.
-/
namespace SpiralLattice

/-- `sumL g l` is the sum of `g x` over the list `l`. -/
def sumL {α : Type} (g : α → Int) : List α → Int
  | [] => 0
  | a :: l => g a + sumL g l

variable {α β : Type}

@[simp] theorem sumL_nil (g : α → Int) : sumL g [] = 0 := rfl
@[simp] theorem sumL_cons (g : α → Int) (a : α) (l : List α) :
    sumL g (a :: l) = g a + sumL g l := rfl

theorem sumL_add (g h : α → Int) (l : List α) :
    sumL (fun x => g x + h x) l = sumL g l + sumL h l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem sumL_sub (g h : α → Int) (l : List α) :
    sumL (fun x => g x - h x) l = sumL g l - sumL h l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem sumL_mul_left (c : Int) (g : α → Int) (l : List α) :
    sumL (fun x => c * g x) l = c * sumL g l := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Int.mul_add]

theorem sumL_const_zero (l : List α) : sumL (fun _ => (0 : Int)) l = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem sumL_const_one (l : List α) : sumL (fun _ => (1 : Int)) l = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; omega

theorem sumL_congr {g h : α → Int} {l : List α} (H : ∀ x ∈ l, g x = h x) :
    sumL g l = sumL h l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [sumL_cons]
    rw [H a (by simp), ih (fun x hx => H x (by simp [hx]))]

theorem sumL_le {g h : α → Int} {l : List α} (H : ∀ x ∈ l, g x ≤ h x) :
    sumL g l ≤ sumL h l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [sumL_cons]
    have h1 := H a (by simp)
    have h2 := ih (fun x hx => H x (by simp [hx]))
    omega

theorem sumL_nonneg {g : α → Int} {l : List α} (H : ∀ x ∈ l, 0 ≤ g x) : 0 ≤ sumL g l := by
  have := sumL_le (g := fun _ => (0 : Int)) (h := g) (l := l) H
  rw [sumL_const_zero] at this
  exact this

/-- Fubini for finite list sums. -/
theorem sumL_comm (g : α → β → Int) (la : List α) (lb : List β) :
    sumL (fun a => sumL (fun b => g a b) lb) la = sumL (fun b => sumL (fun a => g a b) la) lb := by
  induction la with
  | nil => simp [sumL_const_zero]
  | cons a la ih =>
    simp only [sumL_cons]
    rw [ih, ← sumL_add]

theorem sumL_filter (p : α → Bool) (g : α → Int) (l : List α) :
    sumL g (l.filter p) = sumL (fun x => if p x then g x else 0) l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih]

/-- A sum over a duplicate-free list of a "Kronecker delta" picks out one term. -/
theorem sumL_ite_eq [DecidableEq α] (a : α) (c : Int) {l : List α} (hl : l.Nodup) :
    sumL (fun x => if a = x then c else 0) l = if a ∈ l then c else 0 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb : b ∉ l := (List.nodup_cons.mp hl).1
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    simp only [sumL_cons, ih hl', List.mem_cons]
    by_cases hab : a = b
    · subst hab; simp [hb]
    · simp [hab]

theorem sumL_erase [DecidableEq α] (g : α → Int) {a : α} {l : List α} (h : a ∈ l) :
    sumL g l = g a + sumL g (l.erase a) := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hab : b = a
    · subst hab; simp
    · have ha : a ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hab
        · exact h
      have hb : (b :: l).erase a = b :: l.erase a := by
        simp [hab]
      rw [hb]; simp only [sumL_cons]; rw [ih ha]; omega

theorem exists_ne_zero_of_sumL_ne_zero {g : α → Int} {l : List α} (h : sumL g l ≠ 0) :
    ∃ x ∈ l, g x ≠ 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : g a = 0
    · simp only [sumL_cons, ha, Int.zero_add] at h
      obtain ⟨x, hx, hgx⟩ := ih h
      exact ⟨x, by simp [hx], hgx⟩
    · exact ⟨a, by simp, ha⟩

theorem sumL_ite_one_eq_length (p : α → Bool) (l : List α) :
    sumL (fun x => if p x then (1 : Int) else 0) l = (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih] <;> omega

theorem sumL_flatMap (g : β → Int) (f : α → List β) (l : List α) :
    sumL g (l.flatMap f) = sumL (fun a => sumL g (f a)) l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, sumL_cons]
    rw [← ih]
    generalize f a = m
    induction m with
    | nil => simp
    | cons b m ihm => simp [ihm]; omega

end SpiralLattice
