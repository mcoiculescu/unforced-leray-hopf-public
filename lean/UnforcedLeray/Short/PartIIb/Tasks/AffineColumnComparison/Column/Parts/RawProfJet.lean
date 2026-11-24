import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_8
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.TrainDiff

/-!
# Part II-b, task `PartII-b:G4/3/7/8` (`RawProfJet`): jets of the raw profile

Source of record: `the November 2 reference manuscript`, SP 2419-2423.

Proof. `RawJetBound` bounds the jet sums of `train` and of the scalar `raisedProf` (the terms
`‖·‖` of `train` and `|·|` of `raisedProf`). Here `chartJet (trainProf p) x` is literally the first
block, and `chartJet (raisedMerid p) x = chartJet (raisedProf p • m1) x` equals the second block
(`‖m1‖ = 1`, derivatives of `h • m1` are `(∂h) • m1`). Since `rawProf p = trainProf p + ε • raisedMerid p`
with `0 ≤ ε ≤ 1` (`ε = exp(-d/ν)`), `chartJet` is subadditive along this sum for differentiable
summands (`TrainDiff`), so the raw jet is bounded by the same bound (we keep `C`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

namespace RawProfJetHelp

/-- Subadditivity of the chart jet along `f + ε • g` for `0 ≤ ε ≤ 1` at a point where `f`, `g`
are differentiable. -/
theorem chartJet_add_smul {f g : Coord → Axi.Merid} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (x : Coord) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    chartJet (fun y => f y + ε • g y) x ≤ chartJet f x + chartJet g x := by
  have hH : HasFDerivAt (fun y => f y + ε • g y) (fderiv ℝ f x + ε • fderiv ℝ g x) x :=
    hf.hasFDerivAt.add (hg.hasFDerivAt.const_smul ε)
  have hD : fderiv ℝ (fun y => f y + ε • g y) x = fderiv ℝ f x + ε • fderiv ℝ g x := hH.fderiv
  have hv : ∀ v : Coord, fderiv ℝ (fun y => f y + ε • g y) x v =
      fderiv ℝ f x v + ε • fderiv ℝ g x v := by
    intro v
    rw [hD]
    simp
  have hS : Axi.dS (fun y => f y + ε • g y) x = Axi.dS f x + ε • Axi.dS g x := hv _
  have hQ : Axi.dQ (fun y => f y + ε • g y) x = Axi.dQ f x + ε • Axi.dQ g x := hv _
  have hE : Axi.dEta (fun y => f y + ε • g y) x = Axi.dEta f x + ε • Axi.dEta g x := hv _
  have hK : kAge (fun y => f y + ε • g y) x = kAge f x + ε • kAge g x := by
    unfold kAge
    rw [hS, hE]
    module
  have key : ∀ a b : Axi.Merid, ‖a + ε • b‖ ≤ ‖a‖ + ‖b‖ := by
    intro a b
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hε0]
    have := mul_le_of_le_one_left (norm_nonneg b) hε1
    linarith
  unfold chartJet
  rw [hQ, hE, hK]
  have h1 := key (f x) (g x)
  have h2 := key (Axi.dQ f x) (Axi.dQ g x)
  have h3 := key (Axi.dEta f x) (Axi.dEta g x)
  have h4 := key (kAge f x) (kAge g x)
  show ‖f x + ε • g x‖ + ‖Axi.dQ f x + ε • Axi.dQ g x‖ + ‖Axi.dEta f x + ε • Axi.dEta g x‖
      + ‖kAge f x + ε • kAge g x‖ ≤ _
  linarith

/-- The chart jet of a scalar multiple of the fixed unit meridional vector `m1` (`‖m1‖ = 1`): it is
the sum of the absolute values of the scalar jets. -/
theorem chartJet_smul_m1 {h : Coord → ℝ} (x : Coord)
    (hG : DifferentiableAt ℝ (fun y => h y • Axi.m1) x) :
    chartJet (fun y => h y • Axi.m1) x =
      |h x| + |Axi.dQ h x| + |Axi.dEta h x| + |kAge h x| := by
  have hh : DifferentiableAt ℝ h x := by
    have hφ : DifferentiableAt ℝ (fun y => (EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ)
        (h y • Axi.m1)) x :=
      (EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).differentiableAt.comp x hG
    have e : (fun y => (EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ)
        (h y • Axi.m1)) = h := by
      funext y
      simp [Axi.m1]
    rw [e] at hφ
    exact hφ
  have hm : ‖Axi.m1‖ = 1 := by
    simp [Axi.m1]
  have hS : Axi.dS (fun y => h y • Axi.m1) x = Axi.dS h x • Axi.m1 := by
    unfold Axi.dS
    rw [fderiv_smul_const hh, ContinuousLinearMap.smulRight_apply]
  have hQ : Axi.dQ (fun y => h y • Axi.m1) x = Axi.dQ h x • Axi.m1 := by
    unfold Axi.dQ
    rw [fderiv_smul_const hh, ContinuousLinearMap.smulRight_apply]
  have hE : Axi.dEta (fun y => h y • Axi.m1) x = Axi.dEta h x • Axi.m1 := by
    unfold Axi.dEta
    rw [fderiv_smul_const hh, ContinuousLinearMap.smulRight_apply]
  have hK : kAge (fun y => h y • Axi.m1) x = kAge h x • Axi.m1 := by
    unfold kAge
    rw [hS, hE]
    module
  unfold chartJet
  rw [hQ, hE, hK]
  simp [norm_smul, hm, Real.norm_eq_abs]

end RawProfJetHelp

open RawProfJetHelp

/-- **Jets of the raw profile** (SP 2419-2423), from the jet bound on the train and the raised
stream. -/
theorem rawProfJet_of (hR : UnforcedLeray.Short.IIb.RawJetBound) :
    UnforcedLeray.Short.IIb.RawProfJet := by
  intro Sig hSig dm dp hdm
  obtain ⟨C, k, N, ν₀, hC, hν₀, HR⟩ := hR Sig hSig dm dp hdm
  refine ⟨C, k, N, min ν₀ 1, hC, lt_min hν₀ one_pos, min_le_right _ _, ?_⟩
  intro p d hreg hν hS x hx0 hxH
  have hν' : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have HB := HR p d hreg hν' hS x hx0 hxH
  obtain ⟨hTd, hRd⟩ := trainDiff p d dm dp hreg x hx0
  have hRe : DifferentiableAt ℝ (fun y => raisedProf p y • Axi.m1) x := hRd
  have hJr : chartJet (raisedMerid p) x =
      |raisedProf p x| + |Axi.dQ (raisedProf p) x| + |Axi.dEta (raisedProf p) x|
        + |kAge (raisedProf p) x| :=
    chartJet_smul_m1 x hRe
  have hpos : 0 ≤ |raisedProf p x| + |Axi.dQ (raisedProf p) x| + |Axi.dEta (raisedProf p) x|
      + |kAge (raisedProf p) x| := by positivity
  have hJt : chartJet (trainProf p) x ≤
      C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N := by
    unfold chartJet
    linarith [HB, hpos]
  have hJr' : chartJet (raisedMerid p) x ≤
      C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N := by
    rw [hJr]
    have : 0 ≤ ‖trainProf p x‖ + ‖Axi.dQ (trainProf p) x‖ + ‖Axi.dEta (trainProf p) x‖ +
        ‖kAge (trainProf p) x‖ := by positivity
    linarith [HB]
  -- the raw profile is `trainProf + ε • raisedMerid`
  have hreg' := hreg.eps_eq
  have hd0 : 0 ≤ d := le_trans hreg.dm_pos.le hreg.dm_le
  have hνpos : 0 < p.ν := p.ν_pos
  have hε0 : 0 ≤ p.ε := by rw [hreg']; exact (Real.exp_pos _).le
  have hε1 : p.ε ≤ 1 := by
    rw [hreg', Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (div_nonneg hd0 hνpos.le)
  have hsum : chartJet (trainProf p) x + chartJet (raisedMerid p) x ≤
      C * (p.ν ^ k)⁻¹ * (1 + |x.2.2|) ^ N := by
    have e : chartJet (trainProf p) x = ‖trainProf p x‖ + ‖Axi.dQ (trainProf p) x‖ +
        ‖Axi.dEta (trainProf p) x‖ + ‖kAge (trainProf p) x‖ := rfl
    rw [e, hJr]
    linarith [HB]
  refine ⟨hJt, hJr', ?_⟩
  rw [rawProf_eq]
  refine le_trans (chartJet_add_smul hε0 hε1 x hTd hRd) ?_
  linarith [hsum]

end UnforcedLeray.Short.IIb

end
