import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.DivEpsReal

/-!
# `PartIII-b:C/near/masked/8`: `StressMapReal` from `TepsReal`, `TensorTestDense`,
`TensorTestDivMem` (source 1675-1679)

Route: approximate a real tensor `F` by tests `M_n` (`TensorTestDense`), replace them by their
componentwise real parts (still tests, closer to the real `F`), `S'(Re M_n) = T_ε G_n` with `G_n`
real (`smul_divEps_im`), hence real by `TepsReal`; the real fields form a closed set (kernel of the
continuous real-linear map `g ↦ Im g`), and `S'` is continuous.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

open UnforcedLeray.Short.PartIIa in
/-- Componentwise real part on tensors, real-linear. -/
def realTLin : TensorVal →ₗ[ℝ] TensorVal where
  toFun w := WithLp.toLp 2 fun i => (((w i).re : ℝ) : ℂ)
  map_add' w w' := by
    ext i
    simp
  map_smul' a w := by
    ext i
    simp

open UnforcedLeray.Short.PartIIa in
/-- Componentwise real part on tensors, continuous. -/
def realTL : TensorVal →L[ℝ] TensorVal := LinearMap.toContinuousLinearMap realTLin

open UnforcedLeray.Short.PartIIa in
theorem realTL_apply (w : TensorVal) (i : Fin 4) : realTL w i = (((w i).re : ℝ) : ℂ) := rfl

open UnforcedLeray.Short.PartIIa in
theorem realTL_norm_le (w : TensorVal) : ‖realTL w‖ ≤ ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have h : ‖realTL w i‖ ≤ ‖w i‖ := by
    rw [realTL_apply, Complex.norm_real, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

open UnforcedLeray.Short.PartIIa in
theorem realTL_of_real (w : TensorVal) (h : ∀ i, (w i).im = 0) : realTL w = w := by
  ext i
  rw [realTL_apply]
  exact Complex.ext (by simp) (by simp [h i])

open UnforcedLeray.Short.PartIIa in
theorem realTL_im (w : TensorVal) (i : Fin 4) : (realTL w i).im = 0 := by
  rw [realTL_apply]; simp

open UnforcedLeray.Short.PartIIa in
/-- The real part of a tensor test is a tensor test. -/
theorem isTensorTest_realT (c : ℝ) (M : UnforcedLeray.B0220.Profile → TensorVal)
    (h : IsTensorTest c M) : IsTensorTest c (fun p => realTL (M p)) := by
  refine ⟨realTL.contDiff.comp h.smooth, ?_, ?_⟩
  · have hp := h.periodic
    unfold UnforcedLeray.B0220.QPeriodic at hp ⊢
    intro p
    simp only [hp p]
  · obtain ⟨s0, s1, L, hs0, hb⟩ := h.band
    refine ⟨s0, s1, L, hs0, fun p hp => hb p ?_⟩
    intro h0
    apply hp
    simp [h0]

/-- The imaginary part of a complex meridional vector, as a real-linear map. -/
def merImLin : UnforcedLeray.B0223.MeridC →ₗ[ℝ] Merid where
  toFun g := WithLp.toLp 2 fun i => (g i).im
  map_add' g g' := by
    ext i
    simp
  map_smul' a g := by
    ext i
    simp

def merImL : UnforcedLeray.B0223.MeridC →L[ℝ] Merid := LinearMap.toContinuousLinearMap merImLin

theorem isRealH_closed (c : ℝ) :
    IsClosed {g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC | IsRealH c g} := by
  have hc : Continuous (merImL.compLpL (p := 2) (μ := UnforcedLeray.B0220.measureH c)) :=
    ContinuousLinearMap.continuous _
  have : {g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC | IsRealH c g} =
      (merImL.compLpL (p := 2) (μ := UnforcedLeray.B0220.measureH c)) ⁻¹' {0} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [Lp.eq_zero_iff_ae_eq_zero]
    constructor
    · intro h
      filter_upwards [ContinuousLinearMap.coeFn_compLpL merImL g, h, Lp.coeFn_zero Merid 2
        (UnforcedLeray.B0220.measureH c)] with p h1 h2 h3
      rw [h1]
      ext i
      simp [merImL, merImLin, h2 i]
    · intro h
      filter_upwards [ContinuousLinearMap.coeFn_compLpL merImL g, h] with p h1 h2 i
      have := congrArg (fun v : Merid => v i) h2
      simp only [Pi.zero_apply] at h1 this
      rw [h1] at this
      simpa [merImL, merImLin] using this
  rw [this]
  exact isClosed_singleton.preimage hc

open UnforcedLeray.Short.PartIIa in
theorem stressMapReal_of (hT : TepsReal) (hD : TensorTestDense) (hM : TensorTestDivMem) :
    StressMapReal := by
  intro ν ε c P hPf hν hε hc hP μ hμ S' hS F hF
  have hcl := isRealH_closed c
  have hex : ∀ n : ℕ, ∃ M : UnforcedLeray.B0220.Profile → TensorVal, IsTensorTest c M ∧
      ∃ h : MemLp M 2 (measureHT c), ‖F - h.toLp M‖ < 1 / ((n : ℝ) + 1) :=
    fun n => hD c hc F _ (by positivity)
  choose M hMt hMem hMn using hex
  have hRmem : ∀ n, MemLp (fun p => realTL (M n p)) 2 (measureHT c) :=
    fun n => realTL.comp_memLp' (hMem n)
  set R : ℕ → HTSpace c := fun n => (hRmem n).toLp (fun p => realTL (M n p)) with hRdef
  have hRF : ∀ n, ‖R n - F‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : ‖R n - F‖ ≤ ‖F - (hMem n).toLp (M n)‖ := by
      rw [← norm_neg (F - _), neg_sub]
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_sub (R n) F, Lp.coeFn_sub ((hMem n).toLp (M n)) F,
        (hRmem n).coeFn_toLp, (hMem n).coeFn_toLp, hF] with p h1 h2 h3 h4 h5
      rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4]
      have : (F : UnforcedLeray.B0220.Profile → TensorVal) p = realTL (F p) :=
        (realTL_of_real _ h5).symm
      conv_lhs => rw [this]
      rw [← map_sub]
      exact realTL_norm_le _
    exact h1.trans (hMn n).le
  have hlim : Filter.Tendsto R Filter.atTop (nhds F) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hRF tendsto_one_div_add_atTop_nhds_zero_nat
  have hGmem : ∀ n, MemLp (fun p => (p.1 : ℂ) • divEps ε (fun p => realTL (M n p)) p) 2
      (UnforcedLeray.B0220.measureH c) :=
    fun n => hM c ε hc _ (isTensorTest_realT c _ (hMt n))
  have hreal : ∀ n, IsRealH c (S' (R n)) := by
    intro n
    set G : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC :=
      (hGmem n).toLp _ with hG
    have h1 : S' (R n) = UnforcedLeray.Short.PartIIa.Teps hν hε hc hP (μ : ℂ) G :=
      hS (fun p => realTL (M n p)) (isTensorTest_realT c _ (hMt n)) (R n) G
        (hRmem n).coeFn_toLp (hGmem n).coeFn_toLp
    rw [h1]
    refine hT ν ε c P hν hε hc hP μ hμ G ?_
    filter_upwards [(hGmem n).coeFn_toLp] with p hp i
    rw [hG, hp]
    exact smul_divEps_im ε _ (fun p i => realTL_im _ i) p i
  exact hcl.mem_of_tendsto ((S'.continuous.tendsto F).comp hlim)
    (Filter.Eventually.of_forall hreal)

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
