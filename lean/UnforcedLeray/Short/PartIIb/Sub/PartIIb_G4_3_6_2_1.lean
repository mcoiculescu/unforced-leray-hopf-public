import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2

/-!
# Part II-b, task `PartII-b:G4/3/6/2/1` (`RaisedChartBridge`): decomposition

Source of record: `the November 2 reference manuscript` (SP) 2412-2423, 1206-1216
(`H = ψ - η∂_ηψ - 2s∂_sψ = (1-K)ψ`, `K = 2s∂_s + η∂_η`).

For a function `ψ : ℝ → Plane → ℝ` jointly smooth on `s > 0`, put `Ψ(s,(q,η)) = ψ s (q,η)` and
`raisedH ψ = Ψ - η dEta Ψ - 2 s dS Ψ`.  The chart derivatives of `raisedH ψ` are explicit
(`RaisedFormula`, a product rule), and the second derivatives of `Ψ` occurring are bounded by the
age/space jets of `ψ` (`RaisedJetFirst`, `RaisedJetMixed`, `RaisedJetSecond`, with the symmetry of
mixed partials `RaisedSymm`).  Proved here: `raisedChartBridge_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartI

/-- The chart function `Ψ(s,(q,η)) = ψ s (q,η)`. -/
def psiChart (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ) : Coord → ℝ := fun y => ψ y.1 y.2

/-- `H = Ψ - η ∂_ηΨ - 2s ∂_sΨ` with the chart partials `Axi.dEta`, `Axi.dS` (SP 2419). -/
def raisedH (ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ) : Coord → ℝ := fun y =>
  psiChart ψ y - y.2.2 * Axi.dEta (psiChart ψ) y - 2 * y.1 * Axi.dS (psiChart ψ) y

/-- `C03.raisedStream` is `raisedH` for `s > 0` (the slice derivatives are the chart partials of the
jointly smooth `Ψ`). -/
def RaisedStreamEq : Prop :=
  ∀ ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ,
    ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) →
    ∀ y : Coord, 0 < y.1 →
      UnforcedLeray.Cons.C03.raisedStream ψ y.1 y.2.1 y.2.2 = raisedH ψ y

/-- Product rule: for every chart direction `e`,
`D_e H = D_eΨ - e_η ∂_ηΨ - η D_e(∂_ηΨ) - 2 e_s ∂_sΨ - 2s D_e(∂_sΨ)`. -/
def RaisedFormula : Prop :=
  ∀ ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ,
    ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) →
    ∀ x : Coord, 0 < x.1 → ∀ e : Coord,
      fderiv ℝ (raisedH ψ) x e =
        fderiv ℝ (psiChart ψ) x e - e.2.2 * Axi.dEta (psiChart ψ) x
          - x.2.2 * fderiv ℝ (Axi.dEta (psiChart ψ)) x e
          - 2 * e.1 * Axi.dS (psiChart ψ) x - 2 * x.1 * fderiv ℝ (Axi.dS (psiChart ψ)) x e

/-- Zeroth, first, and `∂_s²` bounds by the jets `ageJet ℓ j` (unit vectors have norm one;
`ageJet 2 0 = ∂_s²ψ`, `ageJet 0 1 = Dψ`). -/
def RaisedJetFirst : Prop :=
  ∀ ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ,
    ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) →
    ∀ x : Coord, 0 < x.1 →
      |psiChart ψ x| ≤ ‖ageJet 0 0 ψ x.1 x.2‖ ∧
      |Axi.dS (psiChart ψ) x| ≤ ‖ageJet 1 0 ψ x.1 x.2‖ ∧
      |Axi.dQ (psiChart ψ) x| ≤ ‖ageJet 0 1 ψ x.1 x.2‖ ∧
      |Axi.dEta (psiChart ψ) x| ≤ ‖ageJet 0 1 ψ x.1 x.2‖ ∧
      |fderiv ℝ (Axi.dS (psiChart ψ)) x (1, (0, 0))| ≤ ‖ageJet 2 0 ψ x.1 x.2‖

/-- Mixed bounds: `D_q ∂_sΨ, D_η ∂_sΨ` by `‖ageJet 1 1‖` (`ageJet 1 1 = D_z ∂_sψ`). -/
def RaisedJetMixed : Prop :=
  ∀ ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ,
    ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) →
    ∀ x : Coord, 0 < x.1 →
      |fderiv ℝ (Axi.dS (psiChart ψ)) x (0, (1, 0))| ≤ ‖ageJet 1 1 ψ x.1 x.2‖ ∧
      |fderiv ℝ (Axi.dS (psiChart ψ)) x (0, (0, 1))| ≤ ‖ageJet 1 1 ψ x.1 x.2‖

/-- Second spatial bounds: `D_η ∂_ηΨ, D_q ∂_ηΨ` by `‖ageJet 0 2‖` (`= ‖D²ψ‖`). -/
def RaisedJetSecond : Prop :=
  ∀ ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ,
    ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) →
    ∀ x : Coord, 0 < x.1 →
      |fderiv ℝ (Axi.dEta (psiChart ψ)) x (0, (0, 1))| ≤ ‖ageJet 0 2 ψ x.1 x.2‖ ∧
      |fderiv ℝ (Axi.dEta (psiChart ψ)) x (0, (1, 0))| ≤ ‖ageJet 0 2 ψ x.1 x.2‖

/-- Symmetry of mixed second partials: `∂_s∂_ηΨ = ∂_η∂_sΨ` (`ContDiffAt.isSymmSndFDerivAt`). -/
def RaisedSymm : Prop :=
  ∀ ψ : ℝ → UnforcedLeray.Cyl.Plane → ℝ,
    ContDiffOn ℝ ∞ (psiChart ψ) (Ioi (0 : ℝ) ×ˢ (univ : Set UnforcedLeray.Cyl.Plane)) →
    ∀ x : Coord, 0 < x.1 →
      fderiv ℝ (Axi.dEta (psiChart ψ)) x (1, (0, 0)) =
        fderiv ℝ (Axi.dS (psiChart ψ)) x (0, (0, 1))

private lemma abs_mul_le' {a B : ℝ} (η : ℝ) (h : |a| ≤ B) : |η * a| ≤ |η| * B := by
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

private lemma final_alg (s t B00 B10 B01 B20 B11 B02 : ℝ) (hs0 : 0 < s) (ht0 : 0 ≤ t)
    (n00 : 0 ≤ B00) (n10 : 0 ≤ B10) (n01 : 0 ≤ B01) (n20 : 0 ≤ B20) (n11 : 0 ≤ B11)
    (n02 : 0 ≤ B02) {h q e k : ℝ}
    (HH : h ≤ B00 + t * B01 + 2 * s * B10) (QH : q ≤ B01 + t * B02 + 2 * s * B11)
    (EH : e ≤ t * B02 + 2 * s * B11)
    (KH : k ≤ 2 * s * (B10 + t * B11 + 2 * s * B20) + t * (t * B02 + 2 * s * B11)) :
    h + q + e + k ≤ 20 * (1 + t + s) ^ 2 * (B00 + B10 + B01 + B20 + B11 + B02) := by
  have hst := mul_nonneg hs0.le ht0
  have c1 : 0 ≤ 20 * (1 + t + s) ^ 2 - 1 := by nlinarith
  have c2 : 0 ≤ 20 * (1 + t + s) ^ 2 - (t + 1) := by nlinarith
  have c3 : 0 ≤ 20 * (1 + t + s) ^ 2 - 4 * s := by nlinarith
  have c4 : 0 ≤ 20 * (1 + t + s) ^ 2 - (2 * t + t ^ 2) := by nlinarith
  have c5 : 0 ≤ 20 * (1 + t + s) ^ 2 - (4 * s + 4 * s * t) := by nlinarith
  have c6 : 0 ≤ 20 * (1 + t + s) ^ 2 - 4 * s ^ 2 := by nlinarith
  nlinarith [mul_nonneg c1 n00, mul_nonneg c2 n01, mul_nonneg c3 n10, mul_nonneg c4 n02,
    mul_nonneg c5 n11, mul_nonneg c6 n20]

/-- **Chart bridge for the raised stream** from the calculus leaves. -/
theorem raisedChartBridge_of (hA : RaisedStreamEq) (hF : RaisedFormula) (h1 : RaisedJetFirst)
    (h2 : RaisedJetMixed) (h3 : RaisedJetSecond) (h4 : RaisedSymm) : RaisedChartBridge := by
  intro p d dm dp hd x hx
  have hsm := hd.train_stream_smooth
  change ContDiffOn ℝ ∞ (psiChart p.train.ψ) _ at hsm
  set ψ := p.train.ψ with hψ
  have hev : raisedProf p =ᶠ[𝓝 x] raisedH ψ := by
    have hopen : IsOpen {y : Coord | 0 < y.1} := isOpen_lt continuous_const continuous_fst
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hA ψ hsm y hy
  have hfd : fderiv ℝ (raisedProf p) x = fderiv ℝ (raisedH ψ) x := hev.fderiv_eq
  have hH : raisedProf p x = raisedH ψ x := hev.eq_of_nhds
  obtain ⟨b00, bS, bQ, bE, bSS⟩ := h1 ψ hsm x hx
  obtain ⟨bSQ, bSE⟩ := h2 ψ hsm x hx
  obtain ⟨bEE, bEQ⟩ := h3 ψ hsm x hx
  have hsy := h4 ψ hsm x hx
  have fS := hF ψ hsm x hx (1, (0, 0))
  have fQ := hF ψ hsm x hx (0, (1, 0))
  have fE := hF ψ hsm x hx (0, (0, 1))
  have eQ : Axi.dQ (raisedProf p) x = fderiv ℝ (raisedH ψ) x (0, (1, 0)) := by
    unfold Axi.dQ; rw [hfd]
  have eE : Axi.dEta (raisedProf p) x = fderiv ℝ (raisedH ψ) x (0, (0, 1)) := by
    unfold Axi.dEta; rw [hfd]
  have eS : Axi.dS (raisedProf p) x = fderiv ℝ (raisedH ψ) x (1, (0, 0)) := by
    unfold Axi.dS; rw [hfd]
  simp only [mul_zero, mul_one, sub_zero, zero_mul, one_mul, sub_self, zero_sub] at fS fQ fE
  have dQd : fderiv ℝ (psiChart ψ) x (0, (1, 0)) = Axi.dQ (psiChart ψ) x := rfl
  have dEd : fderiv ℝ (psiChart ψ) x (0, (0, 1)) = Axi.dEta (psiChart ψ) x := rfl
  have dSd : fderiv ℝ (psiChart ψ) x (1, (0, 0)) = Axi.dS (psiChart ψ) x := rfl
  rw [dQd] at fQ
  rw [dEd] at fE
  rw [dSd] at fS
  set s := x.1 with hs
  set η := x.2.2 with hη
  set t := |η| with ht
  have hs0 : 0 < s := hx
  have ht0 : 0 ≤ t := abs_nonneg _
  set B00 := ‖ageJet 0 0 ψ x.1 x.2‖
  set B10 := ‖ageJet 1 0 ψ x.1 x.2‖
  set B01 := ‖ageJet 0 1 ψ x.1 x.2‖
  set B20 := ‖ageJet 2 0 ψ x.1 x.2‖
  set B11 := ‖ageJet 1 1 ψ x.1 x.2‖
  set B02 := ‖ageJet 0 2 ψ x.1 x.2‖
  have n00 : 0 ≤ B00 := norm_nonneg _
  have n10 : 0 ≤ B10 := norm_nonneg _
  have n01 : 0 ≤ B01 := norm_nonneg _
  have n20 : 0 ≤ B20 := norm_nonneg _
  have n11 : 0 ≤ B11 := norm_nonneg _
  have n02 : 0 ≤ B02 := norm_nonneg _
  have habs : ∀ (c a B : ℝ), |a| ≤ B → |c * a| ≤ |c| * B := fun c a B h => abs_mul_le' c h
  have hs2 : ∀ (a B : ℝ), |a| ≤ B → |2 * s * a| ≤ 2 * s * B := by
    intro a B h
    have := habs (2 * s) a B h
    rwa [abs_of_pos (by positivity : (0:ℝ) < 2 * s)] at this
  -- the four chart quantities
  have QH : |Axi.dQ (raisedProf p) x| ≤ B01 + t * B02 + 2 * s * B11 := by
    rw [eQ, fQ]
    have a1 := habs η _ _ bEQ
    have a2 := hs2 _ _ bSQ
    have a3 := abs_le.1 bQ
    have a4 := abs_le.1 a1
    have a5 := abs_le.1 a2
    rw [abs_le]; constructor <;> linarith
  have EH : |Axi.dEta (raisedProf p) x| ≤ t * B02 + 2 * s * B11 := by
    rw [eE, fE]
    have a1 := habs η _ _ bEE
    have a2 := hs2 _ _ bSE
    have a4 := abs_le.1 a1
    have a5 := abs_le.1 a2
    rw [abs_le]; constructor <;> linarith
  have SH : |Axi.dS (raisedProf p) x| ≤ B10 + t * B11 + 2 * s * B20 := by
    rw [eS, fS, hsy]
    have a1 := habs η _ _ bSE
    have a2 := hs2 _ _ bSS
    have a3 := abs_le.1 bS
    have a4 := abs_le.1 a1
    have a5 := abs_le.1 a2
    rw [abs_le]; constructor <;> linarith
  have HH : |raisedProf p x| ≤ B00 + t * B01 + 2 * s * B10 := by
    rw [hH]
    show |psiChart ψ x - η * Axi.dEta (psiChart ψ) x - 2 * s * Axi.dS (psiChart ψ) x| ≤ _
    have a1 := habs η _ _ bE
    have a2 := hs2 _ _ bS
    have a3 := abs_le.1 b00
    have a4 := abs_le.1 a1
    have a5 := abs_le.1 a2
    rw [abs_le]; constructor <;> linarith
  have KH : |kAge (raisedProf p) x| ≤
      2 * s * (B10 + t * B11 + 2 * s * B20) + t * (t * B02 + 2 * s * B11) := by
    unfold kAge
    show |(2 * s) • Axi.dS (raisedProf p) x + η • Axi.dEta (raisedProf p) x| ≤ _
    simp only [smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact hs2 _ _ SH
    · exact habs η _ _ EH
  exact final_alg s t B00 B10 B01 B20 B11 B02 hs0 ht0 n00 n10 n01 n20 n11 n02 HH QH EH KH

end UnforcedLeray.Short.IIb
