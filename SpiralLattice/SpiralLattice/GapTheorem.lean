/-
SpiralLattice.GapTheorem — with no charges, the lightest excitation is one plaquette.

  GP1 ★★  (chirality ⟹ even energy)  On a lattice whose two spiral chiralities alternate
          (bipartite), every divergence-free integer flux has even energy.
  GP2 ★★  (no short loops)  On a simple lattice, a non-zero divergence-free integer flux has
          at least three links with non-zero flux, so energy ≥ 3.
  GP3 ★★★ (strong-coupling gap)  Combining GP1 and GP2: energy ∈ {0} ∪ {4, 6, 8, …}.
          The gap is 4 units of g²/2a, i.e. Δ = 2g²/a at leading order in strong coupling.
  GP4     The bound is attained: a unit flux around one plaquette of ℤ² has energy exactly 4.
-/
import SpiralLattice.Hypercubic

namespace SpiralLattice

variable {V : Type} [DecidableEq V]

theorem pairwise_mem {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : R a b ∨ R b a := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hab
      · exact Or.inl (h.1 b hb')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (h.1 a ha')
      · exact ih h.2 ha' hb'

theorem Simple.nodup {c : List (Link V)} (h : Simple c) : c.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  refine h.2.imp ?_
  intro a b hab heq
  subst heq
  exact hab (Or.inl ⟨rfl, rfl⟩)

theorem sumL_emod_two_zero {α : Type} {g : α → Int} {l : List α} (h : ∀ x ∈ l, g x % 2 = 0) :
    sumL g l % 2 = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [sumL_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    omega

/-- GP1 ★★ Alternating chiralities force even energy for divergence-free flux. -/
theorem energy_even (c : List (Link V)) (vs : List V) (hc : Covers vs c)
    (p : V → Bool) (hbip : Bipartite p c) (hfree : ∀ z ∈ vs, div c z = 0) :
    energy c % 2 = 0 := by
  have hg := gauss_region c vs hc p
  have h0 : sumL (div c) (vs.filter p) = 0 := by
    rw [sumL_congr (fun z hz => hfree z (List.mem_filter.mp hz).1), sumL_const_zero]
  rw [h0] at hg
  -- each link contributes ± flux, which has the parity of flux², so energy ≡ netOut ≡ 0
  have hpt : ∀ l ∈ c, (l.flux * l.flux - l.flux * (ind p l.tail - ind p l.head)) % 2 = 0 := by
    intro l hl
    have hb := hbip l hl
    unfold ind
    by_cases a : p l.tail <;> by_cases b : p l.head <;> simp [a, b] at hb ⊢
    · exact sq_sub_self_even l.flux
    · have := sq_sub_self_even l.flux
      have e : l.flux * l.flux + l.flux = (l.flux * l.flux - l.flux) + 2 * l.flux := by omega
      rw [e]; omega
  have hsum := sumL_emod_two_zero hpt
  have := sumL_sub (fun l => l.flux * l.flux) (fun l => l.flux * (ind p l.tail - ind p l.head)) c
  unfold energy
  unfold netOut at hg
  omega

theorem out_ne_zero_incident {l : Link V} {x : V} (h : l.out x ≠ 0) :
    (l.tail = x ∨ l.head = x) ∧ l.flux ≠ 0 := by
  unfold Link.out at h
  by_cases h1 : l.tail = x <;> by_cases h2 : l.head = x <;> simp_all

/-- GP2 ★★ A non-zero divergence-free flux on a simple lattice uses at least three links. -/
theorem energy_ge_three (c : List (Link V)) (vs : List V) (hc : Covers vs c)
    (hs : Simple c) (hfree : ∀ z ∈ vs, div c z = 0)
    (l1 : Link V) (hl1 : l1 ∈ c) (hf1 : l1.flux ≠ 0) : 3 ≤ energy c := by
  have hnd := hs.nodup
  have hloop := hs.1 l1 hl1
  -- at the tail of l1 some other link carries flux
  have hA : div c l1.tail = 0 := hfree _ (hc.2 l1 hl1).1
  have hB : div c l1.head = 0 := hfree _ (hc.2 l1 hl1).2
  unfold div at hA hB
  rw [sumL_erase _ hl1] at hA hB
  have oA : l1.out l1.tail = l1.flux := by simp [Link.out, Ne.symm hloop]
  have oB : l1.out l1.head = -l1.flux := by
    simp [Link.out, hloop]
  rw [oA] at hA
  rw [oB] at hB
  have hA' : sumL (fun l => l.out l1.tail) (c.erase l1) ≠ 0 := by omega
  have hB' : sumL (fun l => l.out l1.head) (c.erase l1) ≠ 0 := by omega
  obtain ⟨l2, hl2, ho2⟩ := exists_ne_zero_of_sumL_ne_zero hA'
  obtain ⟨l3, hl3, ho3⟩ := exists_ne_zero_of_sumL_ne_zero hB'
  obtain ⟨inc2, hf2⟩ := out_ne_zero_incident ho2
  obtain ⟨inc3, hf3⟩ := out_ne_zero_incident ho3
  have hl2c : l2 ∈ c := List.mem_of_mem_erase hl2
  have hl3c : l3 ∈ c := List.mem_of_mem_erase hl3
  have h21 : l2 ≠ l1 := fun e => (hnd.not_mem_erase (a := l1)) (e ▸ hl2)
  have h31 : l3 ≠ l1 := fun e => (hnd.not_mem_erase (a := l1)) (e ▸ hl3)
  have h23 : l2 ≠ l3 := by
    intro e
    subst e
    have hl2loop := hs.1 l2 hl2c
    have hsame : sameEnds l1 l2 := by
      unfold sameEnds
      rcases inc2 with t2 | h2 <;> rcases inc3 with t3 | h3
      · exact absurd (t2.symm.trans t3) hloop
      · exact Or.inl ⟨t2.symm, h3.symm⟩
      · exact Or.inr ⟨h2.symm, t3.symm⟩
      · exact absurd (h2.symm.trans h3) hloop
    rcases pairwise_mem hs.2 hl1 hl2c (Ne.symm h21) with h | h
    · exact h hsame
    · apply h
      unfold sameEnds at hsame ⊢
      rcases hsame with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl ⟨a.symm, b.symm⟩
      · exact Or.inr ⟨b.symm, a.symm⟩
  -- count three distinct links with non-zero flux
  have hl3' : l3 ∈ (c.erase l1).erase l2 := (List.mem_erase_of_ne (Ne.symm h23)).mpr hl3
  have e1 := sumL_erase (fun l => l.flux * l.flux) hl1
  have e2 := sumL_erase (fun l => l.flux * l.flux) hl2
  have e3 := sumL_erase (fun l => l.flux * l.flux) hl3'
  have r := sumL_nonneg (g := fun l => l.flux * l.flux)
    (l := ((c.erase l1).erase l2).erase l3) (fun l _ => sq_nonneg' l.flux)
  have s1 := one_le_sq_of_ne_zero hf1
  have s2 := one_le_sq_of_ne_zero hf2
  have s3 := one_le_sq_of_ne_zero hf3
  unfold energy
  omega

/-- GP3 ★★★ Strong-coupling gap: a non-zero divergence-free flux on a simple lattice with
alternating chiralities has energy at least 4 (and even). -/
theorem gap_theorem (c : List (Link V)) (vs : List V) (hc : Covers vs c)
    (hs : Simple c) (p : V → Bool) (hbip : Bipartite p c)
    (hfree : ∀ z ∈ vs, div c z = 0)
    (hne : ∃ l ∈ c, l.flux ≠ 0) :
    4 ≤ energy c ∧ energy c % 2 = 0 := by
  obtain ⟨l, hl, hf⟩ := hne
  have h3 := energy_ge_three c vs hc hs hfree l hl hf
  have h2 := energy_even c vs hc p hbip hfree
  exact ⟨by omega, h2⟩

/-! ### GP4: the plaquette attains the bound -/

/-- The four corners of the unit plaquette of ℤ². -/
def sq00 : Fin 2 → Int := fun i => if i = 0 then 0 else 0
def sq10 : Fin 2 → Int := fun i => if i = 0 then 1 else 0
def sq11 : Fin 2 → Int := fun i => if i = 0 then 1 else 1
def sq01 : Fin 2 → Int := fun i => if i = 0 then 0 else 1

/-- Unit flux circulating once around the plaquette (links oriented along +x and +y). -/
def plaquette : List (Link (Fin 2 → Int)) :=
  [⟨sq00, sq10, 1⟩, ⟨sq10, sq11, 1⟩, ⟨sq01, sq11, -1⟩, ⟨sq00, sq01, -1⟩]

def plaquetteSites : List (Fin 2 → Int) := [sq00, sq10, sq11, sq01]

/-- Chirality of a site of ℤ²: parity of x + y. -/
def chirality2 (z : Fin 2 → Int) : Bool := (z 0 + z 1) % 2 == 0

theorem plaquette_energy : energy plaquette = 4 := by decide

theorem plaquette_divfree : ∀ z ∈ plaquetteSites, div plaquette z = 0 := by decide

theorem plaquette_bipartite : Bipartite chirality2 plaquette := by
  unfold Bipartite; decide

theorem plaquette_covers : Covers plaquetteSites plaquette := by
  unfold Covers; decide

theorem plaquette_simple : Simple plaquette := by
  unfold Simple sameEnds; decide

theorem plaquette_unit_steps : ∀ l ∈ plaquette, ∃ j, l.head = shift l.tail j := by
  intro l hl
  simp only [plaquette, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩

/-- GP4: the minimum of GP3 is attained, so the strong-coupling gap is exactly 4 units. -/
theorem gap_attained : ∃ c : List (Link (Fin 2 → Int)), ∃ vs,
    Covers vs c ∧ Simple c ∧ Bipartite chirality2 c ∧ (∀ z ∈ vs, div c z = 0) ∧
    (∃ l ∈ c, l.flux ≠ 0) ∧ energy c = 4 :=
  ⟨plaquette, plaquetteSites, plaquette_covers, plaquette_simple, plaquette_bipartite,
    plaquette_divfree, ⟨⟨sq00, sq10, 1⟩, by simp [plaquette], by decide⟩, plaquette_energy⟩

end SpiralLattice
