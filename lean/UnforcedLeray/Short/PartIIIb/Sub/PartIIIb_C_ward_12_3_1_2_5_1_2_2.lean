import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.RingStreamJetsDecay
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.CutStreamSVanish
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLiftJet
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.LerayPairSol

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/2/2` (decomposition): `InletBackgroundBounds`

Source `the November 2 reference manuscript`
lines 1206-1222 (bounds on `raw`), 5283-5295 (the inlet column `E_i`), 2356-2366, 2386-2387
(Cartesian jets of the ring lift).

* `raw`: `RawJointSmooth` (joint smoothness, hence measurability and differentiability) and
  `RawDerivBdd` (orders `0` and `1`), the two source facts of task `.../6/1`.
* `inlet i`: measurable and differentiable from `inlet_contDiff`; bounded by the proved
  `ringLiftJet` (orders `0`, `1`) applied to the profile `inletProfile i`, whose weighted jets come
  from the proved `cutStreamJets`, `ringStreamJetsDecay`, `cutStreamSVanish`; the constants depend
  on `p` (qualitative boundedness), so no smallness beyond `ν ≤ 1` is used and the age cutoff
  need not be fixed.
* `inlet i τ` is solenoidal: smooth and pointwise divergence free (`inlet_div_offAxis` and
  density of the off-axis set); the non-compact version of "smooth + divergence free is
  distributionally solenoidal" is proved here (test functions have compact support).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff
open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Axi UnforcedLeray.Blueprint
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.IIb.LerayPairSolAux in
/-- A smooth field with classically vanishing divergence is distributionally solenoidal (the
test functions have compact support; no support condition on the field). -/
theorem isSolenoidal_of_div_zero_nc {g : Space → Space} (hg : ContDiff ℝ ∞ g)
    (hdiv : ∀ x : Space, ∑ i : Fin 3, fderiv ℝ g x (coordinateVector i) i = 0) :
    IsSolenoidal g := by
  have hgi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun y => g y i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hg
  have hgi_fd : ∀ i : Fin 3, Continuous (fun x => fderiv ℝ (fun y => g y i) x (coordinateVector i)) :=
    fun i => ((hgi i).continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · apply integrable_finsetSum
    intro i _
    exact Continuous.integrable_of_hasCompactSupport
      ((hgi i).continuous.mul (spatialTestDerivative_continuous hφ i))
      ((spatialTestDerivative_compact hφ i).mul_left)
  · have hint : ∀ i : Fin 3, Integrable (fun x => fderiv ℝ (fun y => g y i) x (coordinateVector i) * φ x) := by
      intro i
      exact Continuous.integrable_of_hasCompactSupport ((hgi_fd i).mul hφ.smooth.continuous)
        (hφ.compact.mul_left)
    have hbp : ∀ i : Fin 3, ∫ x, g x i * spatialTestDerivative i φ x =
        -∫ x, fderiv ℝ (fun y => g y i) x (coordinateVector i) * φ x := by
      intro i
      refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hint i) ?_ ?_ ?_ ?_
      · exact Continuous.integrable_of_hasCompactSupport
          ((hgi i).continuous.mul (spatialTestDerivative_continuous hφ i))
          ((spatialTestDerivative_compact hφ i).mul_left)
      · exact Continuous.integrable_of_hasCompactSupport
          ((hgi i).continuous.mul hφ.smooth.continuous) hφ.compact.mul_left
      · intro x _
        exact ((hgi i).differentiable (by simp)) x
      · intro x _
        exact (hφ.smooth.differentiable (by simp)) x
    show ∫ x, ∑ i : Fin 3, g x i * spatialTestDerivative i φ x = 0
    have hint0 : ∀ i : Fin 3, Integrable (fun x => g x i * spatialTestDerivative i φ x) := fun i =>
      Continuous.integrable_of_hasCompactSupport
        ((hgi i).continuous.mul (spatialTestDerivative_continuous hφ i))
        ((spatialTestDerivative_compact hφ i).mul_left)
    rw [integral_finsetSum _ (fun i _ => hint0 i)]
    rw [Finset.sum_congr rfl (fun i _ => hbp i), Finset.sum_neg_distrib,
      ← integral_finsetSum _ (fun i _ => hint i)]
    have hz : (fun x => ∑ i : Fin 3, fderiv ℝ (fun y => g y i) x (coordinateVector i) * φ x) =
        fun _ => 0 := by
      funext x
      simp only [fderiv_proj_apply hg, ← Finset.sum_mul, hdiv x, zero_mul]
    rw [hz]
    simp

/-- `(1 + x) e^{-a x} ≤ 1 + 1/a` for `x ≥ 0`, `a > 0`. -/
theorem weight_exp_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (1 + x) * Real.exp (-(a * x)) ≤ 1 + 1 / a := by
  have h1 : Real.exp (-(a * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h2 : a * x * Real.exp (-(a * x)) ≤ 1 := by
    have := Real.add_one_le_exp (a * x)
    have h3 : Real.exp (a * x) * Real.exp (-(a * x)) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : 0 ≤ Real.exp (-(a * x)) := (Real.exp_pos _).le
    nlinarith
  have h5 : x * Real.exp (-(a * x)) ≤ 1 / a := by
    rw [le_div_iff₀ ha]; nlinarith
  nlinarith

/-- The inlet profile vanishes for ages above `H/2`. -/
theorem inletProfile_vanish {p : Params} (i : Fin 2) (hcut : ContDiff ℝ ∞ (p.cutStream i))
    (x : ℝ × (ℝ × ℝ)) (hx : p.H / 2 < x.1) : p.inletProfile i x = 0 := by
  have hH : 0 < p.H := p.H_pos
  have hcut0 : p.cutStream i x = 0 := by
    unfold Params.cutStream
    simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH hx.le]
  have hev : ∀ᶠ y in 𝓝 x, p.H / 2 < y.1 :=
    (continuous_fst.tendsto x).eventually (lt_mem_nhds hx)
  have hfun : p.cutStream i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hev] with y hy
    unfold Params.cutStream
    simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH hy.le]
  have hfd : fderiv ℝ (p.cutStream i) x = 0 := by
    rw [hfun.fderiv_eq]
    simp
  have hdS : Axi.dS (p.cutStream i) x = 0 := by
    unfold Axi.dS
    rw [hfd]
    simp
  have hdQ : Axi.dQ (p.cutStream i) x = 0 := by
    unfold Axi.dQ
    rw [hfd]
    simp
  have hdE : Axi.dEta (p.cutStream i) x = 0 := by
    unfold Axi.dEta
    rw [hfd]
    simp
  simp [Params.inletProfile, Axi.ringStreamProfile, hdS, hdQ, hdE, hcut0]

/-- **Qualitative global bound of the inlet slices and their gradients.** -/
theorem inlet_bdd {p : Params} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {d dm dp : ℝ}
    (hreg : UnforcedLeray.Short.IIb.BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q)
    (i : Fin 2) :
    ∃ C : ℝ, ∀ (τ : ℝ) (y : Space), ‖p.inlet i τ y‖ ≤ C ∧ ‖fderiv ℝ (p.inlet i τ) y‖ ≤ C := by
  have hνpos : 0 < p.ν := p.ν_pos
  have hH : 0 < p.H := p.H_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hcpos : 0 < p.c := by linarith
  have hR1 : 1 ≤ p.R := by
    have hε : p.ε ≤ 1 := by
      rw [hreg.eps_eq]
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ d / p.ν := div_nonneg (by linarith [hreg.dm_pos, hreg.dm_le]) hνpos.le
      rw [neg_div]; linarith
    show 1 ≤ p.ε⁻¹
    exact one_le_inv₀ p.ε_pos |>.mpr hε
  obtain ⟨C3, κ, N, hC3, hκ, h3'⟩ := UnforcedLeray.Short.IIb.cutStreamJets lam q hq (1 + 1)
  obtain ⟨C4, hC4, h4'⟩ := UnforcedLeray.Short.IIb.ringStreamJetsDecay 1
  obtain ⟨hcutsm, hcut⟩ := h3' p hmode hc1 hH i
  set M : ℝ := C3 * (1 + p.H⁻¹) ^ (1 + 1) * p.c ^ N with hM
  have hM0 : 0 ≤ M := by positivity
  have hring := h4' p.R (p.H / 2) p.c κ M (p.cutStream i) hR1 (by positivity) hcpos hκ hM0
    hcutsm
    (by
      intro x hx
      unfold Params.cutStream
      simp [UnforcedLeray.Cons.C03.Concrete.ageCutoff_eq_zero hH (show p.H / 2 ≤ x.1 from hx.le)])
    (fun x hx => UnforcedLeray.Short.IIb.cutStreamSVanish lam q hq p hmode hc1 hH i x hx)
    (fun l hl x => hcut l hl x)
  set K : ℝ := C4 * (1 + p.H / 2) * (1 + p.c / κ) * M with hK
  have hK0 : 0 ≤ K := by positivity
  have ha : 0 < κ / 2 / p.c := by positivity
  set M' : ℝ := K * (1 + 1 / (κ / 2 / p.c)) with hM'
  have hM'0 : 0 ≤ M' := by positivity
  have hwt : ∀ l ≤ 1, ∀ x : ℝ × (ℝ × ℝ),
      (1 + |x.2.2|) * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤ M' := by
    intro l hl x
    have h1 := hring l hl x
    have h2 := weight_exp_le ha (abs_nonneg x.2.2)
    have h3 : Real.exp (-((κ / 2) * |x.2.2| / p.c)) = Real.exp (-(κ / 2 / p.c * |x.2.2|)) := by
      congr 2
      field_simp
    rw [h3] at h1
    calc (1 + |x.2.2|) * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖
        ≤ (1 + |x.2.2|) * (K * Real.exp (-(κ / 2 / p.c * |x.2.2|))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K * ((1 + |x.2.2|) * Real.exp (-(κ / 2 / p.c * |x.2.2|))) := by ring
      _ ≤ K * (1 + 1 / (κ / 2 / p.c)) := mul_le_mul_of_nonneg_left h2 hK0
  have hb : ContDiff ℝ ∞ (p.inletProfile i) := by
    unfold Params.inletProfile
    exact UnforcedLeray.Short.IIb.inletCD_ringStreamProfile hcutsm
  have hvan := inletProfile_vanish (p := p) i hcutsm
  have hS : 0 < p.H / 2 := by positivity
  obtain ⟨C0, k0, hC0, hJ0⟩ := UnforcedLeray.Short.IIb.ringLiftJet 0
  obtain ⟨C1, k1, hC1, hJ1⟩ := UnforcedLeray.Short.IIb.ringLiftJet 1
  refine ⟨max (C0 * (1 + p.H / 2) ^ k0 * M') (C1 * (1 + p.H / 2) ^ k1 * M'), fun τ y => ⟨?_, ?_⟩⟩
  · have h0 : ∀ l ≤ 0, ∀ x : ℝ × (ℝ × ℝ),
        (1 + |x.2.2|) ^ 0 * ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤ M' := by
      intro l hl x
      have hl0 : l = 0 := by omega
      subst hl0
      have h := hwt 0 (Nat.zero_le _) x
      have h2 : ‖iteratedFDeriv ℝ 0 (p.inletProfile i) x‖ ≤
          (1 + |x.2.2|) * ‖iteratedFDeriv ℝ 0 (p.inletProfile i) x‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (by linarith [abs_nonneg x.2.2])
      rw [pow_zero, one_mul]
      exact h2.trans h
    have := hJ0 (p.H / 2) p.R τ M' (p.inletProfile i) hS hR1 hM'0 hb hvan h0 y
    rw [norm_iteratedFDeriv_zero] at this
    exact le_trans this (le_max_left _ _)
  · have := hJ1 (p.H / 2) p.R τ M' (p.inletProfile i) hS hR1 hM'0 hb hvan
      (fun l hl x => by
        simpa using hwt l hl x) y
    rw [norm_iteratedFDeriv_one] at this
    exact le_trans this (le_max_right _ _)


private theorem contDiff_slice (F : ℝ → Space → Space) (h : ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2))
    (τ : ℝ) : ContDiff ℝ ∞ (F τ) :=
  h.comp (contDiff_const.prodMk contDiff_id)

/-- **`InletBackgroundBounds`** (1206-1222, 5283-5295) from the source facts on `raw`:
joint smoothness (`RawJointSmooth`, task `.../6/1/1`) and bounded derivatives of orders `0`, `1`
(`RawDerivBdd`, task `.../6/1/3`). -/
theorem inletBackgroundBounds_of (h1 : RawJointSmooth) (h2 : RawDerivBdd) :
    InletBackgroundBounds := by
  intro lam q hq dm dp hdm
  obtain ⟨a, ha, H1⟩ := h1 dm dp hdm
  obtain ⟨b, hb, H2⟩ := h2 dm dp hdm
  refine ⟨min (min a b) 1, lt_min (lt_min ha hb) one_pos, fun p d hreg hν hmode z g hg => ?_⟩
  have hνa : p.ν ≤ a := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hνb : p.ν ≤ b := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hraw := H1 p d hreg hνa
  refine ⟨⟨hraw.continuous.aestronglyMeasurable, fun τ => ?_, ?_⟩, fun i => ?_⟩
  · exact ((hraw.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
  · obtain ⟨C0, h0⟩ := H2 p d hreg hνb 0
    obtain ⟨C1, h1'⟩ := H2 p d hreg hνb 1
    refine ⟨max C0 C1, fun τ y => ⟨?_, ?_⟩⟩
    · have : ‖iteratedFDeriv ℝ 0 (p.raw τ) y‖ ≤ C0 := h0 τ y
      rw [norm_iteratedFDeriv_zero] at this
      exact this.trans (le_max_left _ _)
    · have : ‖iteratedFDeriv ℝ 1 (p.raw τ) y‖ ≤ C1 := h1' τ y
      rw [norm_iteratedFDeriv_one] at this
      exact this.trans (le_max_right _ _)
  · have hin := inlet_contDiff hq hreg hν1 hmode i
    have hslice : ∀ τ, ContDiff ℝ ∞ (p.inlet i τ) := fun τ => contDiff_slice (p.inlet i) hin τ
    refine ⟨⟨hin.continuous.aestronglyMeasurable, fun τ => (hslice τ).differentiable (by simp),
      inlet_bdd hq hreg hν1 hmode i⟩, fun τ => ?_⟩
    refine isSolenoidal_of_div_zero_nc (hslice τ) fun y => ?_
    have := divergence_zero_of_offAxis ((hslice τ).of_le (by simp))
      (fun y hy => inlet_div_offAxis hq hreg hν1 hmode i τ hy) y
    simpa [Axi.divergence] using this

end UnforcedLeray.Short.PartIIIb.Concrete
