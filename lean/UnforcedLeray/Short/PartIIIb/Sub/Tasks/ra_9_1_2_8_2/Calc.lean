import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_8

/-!
# Chart calculus for `ringRem` (task `PartIII-b:C/asrc/ra/9/1/2/8/2`)

Source `the November 2 reference manuscript` lines 5034-5039, 4979-4980.
Product-rule / linearity lemmas for the conormal words `wordW` on the open set `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The open chart region `s > 0`. -/
abbrev UC : Set Chart := Ioi 0 ×ˢ univ

theorem isOpen_UC : IsOpen UC := isOpen_Ioi.prod isOpen_univ

theorem mem_UC {p : Chart} (hp : 0 < p.1) : p ∈ UC := ⟨hp, trivial⟩

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cd_fderiv {n : ℕ} {F : Chart → E} (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F UC) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun p => fderiv ℝ F p) UC :=
  h.fderiv_of_isOpen isOpen_UC (by push_cast; exact le_rfl)

theorem cd_opW (a : Fin 3) {n : ℕ} {F : Chart → E}
    (h : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F UC) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (opW a F) UC := by
  have hd := cd_fderiv h
  fin_cases a
  · exact contDiffOn_fst.smul (hd.clm_apply contDiffOn_const)
  · exact hd.clm_apply contDiffOn_const
  · exact hd.clm_apply contDiffOn_const

theorem cd_wordW : ∀ (w : List (Fin 3)) (m : ℕ) {F : Chart → E},
    ContDiffOn ℝ ((m + w.length : ℕ) : WithTop ℕ∞) F UC →
    ContDiffOn ℝ (m : WithTop ℕ∞) (wordW w F) UC
  | [], m, F, h => by simpa [wordW] using h
  | a :: w, m, F, h => by
    have h1 : ContDiffOn ℝ ((m + 1 + w.length : ℕ) : WithTop ℕ∞) F UC := by
      convert h using 2; simp; omega
    have h2 := cd_wordW w (m + 1) h1
    exact cd_opW a h2

theorem diffAt_of_cd {F : Chart → E} (h : ContDiffOn ℝ 1 F UC) {p : Chart} (hp : p ∈ UC) :
    DifferentiableAt ℝ F p :=
  (h.differentiableOn one_ne_zero).differentiableAt (isOpen_UC.mem_nhds hp)

theorem cd_mono {F : Chart → E} {m n : ℕ} (hmn : m ≤ n) (h : ContDiffOn ℝ (n : WithTop ℕ∞) F UC) :
    ContDiffOn ℝ (m : WithTop ℕ∞) F UC :=
  h.of_le (by exact_mod_cast hmn)

theorem fderiv_congr_UC {f g : Chart → E} (h : ∀ p ∈ UC, f p = g p) {p : Chart} (hp : p ∈ UC) :
    fderiv ℝ f p = fderiv ℝ g p := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [isOpen_UC.mem_nhds hp] with x hx using h x hx

theorem opW_congr (a : Fin 3) {f g : Chart → E} (h : ∀ p ∈ UC, f p = g p) :
    ∀ p ∈ UC, opW a f p = opW a g p := by
  intro p hp
  have := fderiv_congr_UC h hp
  fin_cases a <;> simp [opW, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta, this]

theorem wordW_congr : ∀ (w : List (Fin 3)) {f g : Chart → E}, (∀ p ∈ UC, f p = g p) →
    ∀ p ∈ UC, wordW w f p = wordW w g p
  | [], f, g, h => h
  | a :: w, f, g, h => opW_congr a (wordW_congr w h)

theorem opW_add (a : Fin 3) {f g : Chart → E} (hf : ContDiffOn ℝ 1 f UC) (hg : ContDiffOn ℝ 1 g UC) :
    ∀ p ∈ UC, opW a (f + g) p = opW a f p + opW a g p := by
  intro p hp
  have h1 := diffAt_of_cd hf hp
  have h2 := diffAt_of_cd hg hp
  fin_cases a <;> simp [opW, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta, fderiv_add h1 h2, smul_add]

theorem opW_smul (a : Fin 3) (c : ℝ) {f : Chart → E} (hf : ContDiffOn ℝ 1 f UC) :
    ∀ p ∈ UC, opW a (c • f) p = c • opW a f p := by
  intro p hp
  have h1 := diffAt_of_cd hf hp
  fin_cases a <;> simp [opW, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta, fderiv_const_smul h1, smul_comm c]

theorem opW_sub (a : Fin 3) {f g : Chart → E} (hf : ContDiffOn ℝ 1 f UC) (hg : ContDiffOn ℝ 1 g UC) :
    ∀ p ∈ UC, opW a (f - g) p = opW a f p - opW a g p := by
  intro p hp
  have h1 := diffAt_of_cd hf hp
  have h2 := diffAt_of_cd hg hp
  fin_cases a <;> simp [opW, UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta, fderiv_sub h1 h2, smul_sub]

theorem wordW_add : ∀ (w : List (Fin 3)) {f g : Chart → E},
    ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) f UC → ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) g UC →
    ∀ p ∈ UC, wordW w (f + g) p = wordW w f p + wordW w g p
  | [], f, g, _, _ => fun p _ => rfl
  | a :: w, f, g, hf, hg => by
    intro p hp
    have hf' : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) f UC := cd_mono (by simp) hf
    have hg' : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) g UC := cd_mono (by simp) hg
    have ih := wordW_add w hf' hg'
    have e1 : wordW (a :: w) (f + g) p = opW a (wordW w f + wordW w g) p :=
      opW_congr a ih p hp
    rw [e1]
    have c1 : ContDiffOn ℝ 1 (wordW w f) UC := cd_wordW w 1 (by
      convert hf using 2; simp [add_comm])
    have c2 : ContDiffOn ℝ 1 (wordW w g) UC := cd_wordW w 1 (by
      convert hg using 2; simp [add_comm])
    exact opW_add a c1 c2 p hp

theorem wordW_sub : ∀ (w : List (Fin 3)) {f g : Chart → E},
    ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) f UC → ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) g UC →
    ∀ p ∈ UC, wordW w (f - g) p = wordW w f p - wordW w g p
  | [], f, g, _, _ => fun p _ => rfl
  | a :: w, f, g, hf, hg => by
    intro p hp
    have hf' : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) f UC := cd_mono (by simp) hf
    have hg' : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) g UC := cd_mono (by simp) hg
    have ih := wordW_sub w hf' hg'
    have e1 : wordW (a :: w) (f - g) p = opW a (wordW w f - wordW w g) p :=
      opW_congr a ih p hp
    rw [e1]
    have c1 : ContDiffOn ℝ 1 (wordW w f) UC := cd_wordW w 1 (by
      convert hf using 2; simp [add_comm])
    have c2 : ContDiffOn ℝ 1 (wordW w g) UC := cd_wordW w 1 (by
      convert hg using 2; simp [add_comm])
    exact opW_sub a c1 c2 p hp

theorem wordW_smul (c : ℝ) : ∀ (w : List (Fin 3)) {f : Chart → E},
    ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) f UC →
    ∀ p ∈ UC, wordW w (c • f) p = c • wordW w f p
  | [], f, _ => fun p _ => rfl
  | a :: w, f, hf => by
    intro p hp
    have hf' : ContDiffOn ℝ ((w.length : ℕ) : WithTop ℕ∞) f UC := cd_mono (by simp) hf
    have ih := wordW_smul c w hf'
    have e1 : wordW (a :: w) (c • f) p = opW a (c • wordW w f) p :=
      opW_congr a ih p hp
    rw [e1]
    have c1 : ContDiffOn ℝ 1 (wordW w f) UC := cd_wordW w 1 (by
      convert hf using 2; simp [add_comm])
    exact opW_smul a c c1 p hp

theorem wordW_append : ∀ (w v : List (Fin 3)) (F : Chart → E),
    wordW (w ++ v) F = wordW w (wordW v F)
  | [], v, F => rfl
  | a :: w, v, F => by simp [wordW, wordW_append w v F]

end

end UnforcedLeray.Short.PartIIIb.Concrete
