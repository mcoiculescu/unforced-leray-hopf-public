import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2Org
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Young

/-!
# Young support of the raw mean residual (`PartIII-b:C/rep/8/2/5`, source 4161-4166, 5395)

For `1/ν < s` the stream cutoff `χ_y` vanishes near the chart point, so `X^mt`, `Y^mt` vanish on
an open set containing `y = chartY R p`, and so does every term of `wardEXY`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem ms_fderiv_eq_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {y : E}
    (h : f =ᶠ[𝓝 y] fun _ => 0) : fderiv ℝ f y = 0 := by
  rw [h.fderiv_eq]; simp

theorem ms_physPd_zero {f : Space → Space} {y : Space} (h : f =ᶠ[𝓝 y] fun _ => 0) (j : Fin 3) :
    physPd f j y = 0 := by
  unfold physPd
  rw [ms_fderiv_eq_zero h]
  simp

theorem ms_physPd2_zero {f : Space → Space} {y : Space} (h : f =ᶠ[𝓝 y] fun _ => 0) (j l : Fin 3) :
    physPd2 f j l y = 0 := by
  have h2 : (fun y' => physPd f l y') =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [h.eventually_nhds] with y' hy'
    exact ms_physPd_zero hy' l
  show fderiv ℝ (fun y' => physPd f l y') y (coordinateVector j) = 0
  rw [ms_fderiv_eq_zero h2]
  simp

theorem ms_physCdiff_zero (U : Space → Space) {X : Space → Space} {y : Space}
    (h : X =ᶠ[𝓝 y] fun _ => 0) : physCdiff U X y = 0 := by
  unfold physCdiff
  simp [ms_physPd_zero h, ms_physPd2_zero h]

theorem ms_physUUD2_zero (U : Space → Space) {X : Space → Space} {y : Space}
    (h : X =ᶠ[𝓝 y] fun _ => 0) : physUUD2 U X y = 0 := by
  unfold physUUD2
  simp [ms_physPd2_zero h]

theorem ms_physDXp_zero (q : Space → ℝ) {X : Space → Space} {y : Space}
    (h : X =ᶠ[𝓝 y] fun _ => 0) : physDXp X q y = 0 := by
  unfold physDXp
  simp [ms_physPd_zero h]
  rfl

theorem ms_wardEXY_zero (ν μ R : ℝ) (U : ℝ → SpatialField) (pp : ℝ → Space → ℝ)
    {X Y : ℝ → Space → Space} {τ : ℝ} {y : Space}
    (hX : X τ =ᶠ[𝓝 y] fun _ => 0) (hY : Y τ =ᶠ[𝓝 y] fun _ => 0) :
    wardEXY ν μ R U pp X Y τ y = 0 := by
  unfold wardEXY
  rw [ms_fderiv_eq_zero hY]
  simp [ms_physCdiff_zero (U τ) hX, ms_physUUD2_zero (U τ) hX, ms_physDXp_zero (pp τ) hX]

/-- `Y^mt` vanishes on the open set `{(ε cylR y)² < ν}` where `X^mt` does. -/
theorem ms_ymt_zero_of_open {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} (M : Chart → Mat3) (hε : 0 < ε)
    (hY : IsStreamCutoff χy) (y : Vec3) (hy : (ε * cylR y) ^ 2 < ν) :
    YmtFun c ν ε μ χo χy M y = 0 := by
  have hO : IsOpen {y' : Vec3 | (ε * cylR y') ^ 2 < ν} := by
    apply isOpen_lt _ continuous_const
    unfold cylR
    fun_prop
  have hz : ∀ y' ∈ {y' : Vec3 | (ε * cylR y') ^ 2 < ν},
      Xmt c ν ε μ χo χy M y' = 0 := fun y' hy' => young_xmt_zero_open M hε hY hy'
  have hz' : ∀ y' ∈ {y' : Vec3 | (ε * cylR y') ^ 2 < ν},
      fderiv ℝ (Xmt c ν ε μ χo χy M) y' = 0 := by
    intro y' hy'
    apply ms_fderiv_eq_zero
    exact Filter.eventually_of_mem (hO.mem_nhds hy') hz
  have hyO : y ∈ {y' : Vec3 | (ε * cylR y') ^ 2 < ν} := hy
  have hvec : vecLap (Xmt c ν ε μ χo χy M) y = 0 := by
    unfold vecLap
    apply Finset.sum_eq_zero
    intro j _
    have hg : (fun y' => fderiv ℝ (Xmt c ν ε μ χo χy M) y' (Pi.single j 1)) =ᶠ[𝓝 y]
        fun _ => 0 := by
      filter_upwards [hO.mem_nhds hyO] with y' hy'
      rw [hz' y' hy']
      simp
    rw [ms_fderiv_eq_zero hg]
    simp
  unfold YmtFun
  rw [hz' y hyO, hz y hyO, hvec]
  simp

/-- The raw mean residual vanishes for `1/ν < s`. -/
theorem ms_meanSupportAt (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy) : MeanSupportAt Pl K L μ := by
  unfold MeanSupportAt
  intro T p hp
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hεne : L.ε ≠ 0 := hε.ne'
  have hs : 0 < p.1 := lt_trans (one_div_pos.2 hν) hp
  set y0 : Space := NearInst.chartY L.ε⁻¹ p with hy0
  have hdef : WithLp.ofLp y0 = ![L.ε⁻¹ / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] := by
    simp [hy0, NearInst.chartY]
  have hc : cylR (WithLp.ofLp y0) = L.ε⁻¹ / Real.sqrt p.1 := by
    rw [hdef]
    unfold cylR
    have hnn : 0 ≤ L.ε⁻¹ / Real.sqrt p.1 :=
      div_nonneg (inv_nonneg.2 hε.le) (Real.sqrt_nonneg _)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (L.ε⁻¹ / Real.sqrt p.1) ^ 2 + (0 : ℝ) ^ 2 = (L.ε⁻¹ / Real.sqrt p.1) ^ 2 by ring]
    exact Real.sqrt_sq hnn
  have hcyl : (L.ε * cylR (WithLp.ofLp y0)) ^ 2 < L.ν := by
    rw [hc]
    have h1 : L.ε * (L.ε⁻¹ / Real.sqrt p.1) = (Real.sqrt p.1)⁻¹ := by
      field_simp
    rw [h1, inv_pow, Real.sq_sqrt hs.le]
    exact inv_lt_of_inv_lt₀ hν (by simpa [one_div] using hp)
  have hev : ∀ᶠ y' in 𝓝 y0, (L.ε * cylR (WithLp.ofLp y')) ^ 2 < L.ν := by
    have hc' : ContinuousAt (fun y' : Space => (L.ε * cylR (WithLp.ofLp y')) ^ 2) y0 := by
      apply Continuous.continuousAt
      unfold cylR
      fun_prop
    exact hc'.eventually_lt continuousAt_const hcyl
  have hX : ∀ τ' : ℝ, (Xmean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)) τ' =ᶠ[𝓝 y0]
      fun _ => 0 := by
    intro τ'
    filter_upwards [hev] with y' hy'
    show WithLp.toLp 2 (Xmt (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (WithLp.ofLp y')) = 0
    rw [young_xmt_zero_open (thinRep T) hε hχ hy']
    simp
  have hY : ∀ τ' : ℝ, (Ymean (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T)) τ' =ᶠ[𝓝 y0]
      fun _ => 0 := by
    intro τ'
    filter_upwards [hev] with y' hy'
    show WithLp.toLp 2 (YmtFun (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) (WithLp.ofLp y')) = 0
    rw [ms_ymt_zero_of_open (thinRep T) hε hχ _ hy']
    simp
  have hz := ms_wardEXY_zero L.ν μ L.ε⁻¹ (rawU Pl L) (liftP L)
    (hX (NearInst.chartTau L.ε⁻¹ p)) (hY (NearInst.chartTau L.ε⁻¹ p))
  unfold meanERaw coefOf
  rw [hz]
  simp

/-- **The young support of the mean field** along the sequence (source 4161-4166, 5395). -/
theorem meanSupport (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.MeanSupport := by
  unfold SeqData.MeanSupport
  exact Filter.Eventually.of_forall fun n z _ =>
    ms_meanSupportAt D.Pl D.K (D.level n) (D.mu n z) hst.chiY

end UnforcedLeray.Short.PartIIIb.Concrete
