import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.ForceBand
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Kflat.Assembly
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.RhsCont.Bound

/-!
# `IsFlatDuhamelColumn` for the concrete flat setting (source 4594-4612, 4761-4763, 3420-3446,
1650-1689)

Source of record: `the November 2 reference manuscript` (73 pages).

* `operatorColumn_of` : from the free body column (`BodyColumnFlat`, leaf (c)) and the pins
  `IsFreeStress`, `IsFlatMult`, the column `b = R₀h - S₀M₀b` of the near operators is a forced column
  of the train equation `∂_sb + (μ/s)b - νΔb + P₀div(v⊗b + b⊗v) = P₀(s⁻¹h)` (source 4084-4086 in
  flat form, 3420-3440, 1684-1689).  The pin `IsFreeStress` is applied at `M₀b` and at `0`: the
  second components of `M₀b` and of `0` are the same element of `ρ_b^{-1/2}H_T` (`IsFlatMult`), so
  they cancel in the difference whatever `ρ_b`.
* `kcColumn_of` : the Duhamel column `K_cξ_B` of the setting is a forced column with the same force
  (leaves (a), (b)).
* `isFlatDuhamelColumn_of` : the pin `Kflat.IsFlatDuhamelColumn` for `actualFlatSetting D χo ε`
  (uniqueness (d) and the definitional readout (e), `frakT_actual`).
* `flatHomogeneousUnique_of_polyCausal` : (d) from `IIIa.PolyCausal` (source 3426-3446).
* `isFlatDuhamelColumn_of_leaves` : the pin at every small viscosity, from the leaves and
  `PolyCausal`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest IsBiotSavart
  flowIntegrand trainVel)

/-! ## Measures -/

theorem cyl_cell_eq (c : ℝ) : UnforcedLeray.Cyl.cell c = B0579.cell c := by
  simp [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]

theorem volCyl_eq (c : ℝ) :
    (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c) =
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
        ((volume : Measure (ℝ × ℝ)).restrict (B0579.cell c)) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]

theorem avgμ_ac_cell (c : ℝ) :
    UnforcedLeray.Cyl.avgμ c ≪ (volume : Measure (ℝ × ℝ)).restrict (B0579.cell c) := by
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  rw [cyl_cell_eq]
  exact Measure.smul_absolutelyContinuous

theorem ageμ_ac_volCyl (c a : ℝ) :
    ageμ c a ≪ (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  rw [volCyl_eq]
  exact (withDensity_absolutelyContinuous _ _).prod (avgμ_ac_cell c)

theorem volCyl_ac_ageμ {c : ℝ} (hc : 0 < c) (a : ℝ) :
    (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c) ≪ ageμ c a := by
  have h1 : (volume : Measure ℝ).restrict (Ioi (0 : ℝ)) ≪
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
        fun s => ENNReal.ofReal (s ^ a) := by
    refine withDensity_absolutelyContinuous' (measurable_ofReal_rpow _).aemeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs _)).ne'
  have h2 : (volume : Measure (ℝ × ℝ)).restrict (B0579.cell c) ≪ UnforcedLeray.Cyl.avgμ c := by
    rw [← cyl_cell_eq]
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    exact Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  rw [volCyl_eq]
  exact h1.prod h2

theorem ageμ_ac_z1Measure (c mZ : ℝ) : ageμ c (-1 / 2) ≪ z1Measure c mZ := by
  refine withDensity_absolutelyContinuous' ?_ (Eventually.of_forall fun p => ?_)
  · refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
    unfold IIIa.transWeight
    fun_prop
  · have hW : 0 < IIIa.transWeight mZ p := by
      unfold IIIa.transWeight
      exact Real.rpow_pos_of_pos (by positivity) _
    exact (ENNReal.ofReal_pos.2 (pow_pos hW 2)).ne'

theorem oldMeasure_ac_volCyl {c ν : ℝ} (hν : 0 < ν) :
    oldMeasure c ν ≪ (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  rw [volCyl_eq]
  refine Measure.AbsolutelyContinuous.prod (Measure.absolutelyContinuous_of_le
    (Measure.restrict_mono (Ioi_subset_Ioi (by positivity)) le_rfl)) (avgμ_ac_cell c)

theorem ae_ageμ_pos (c a : ℝ) : ∀ᵐ p ∂(ageμ c a), 0 < p.1 := by
  have h := (ageμ_ac_volCyl c a).ae_le
    (ae_restrict_mem (measurableSet_Ioi.prod (B0579.measurableSet_cell c)))
  filter_upwards [h] with p hp
  exact hp.1

/-! ## (c) The column of the near operators -/

theorem merOf_smul (r : ℝ) (v : Vec3) : merOf (r • v) = r • merOf v := by
  ext i
  fin_cases i <;> simp [merOf]

/-- `h = s f_A`: the coefficient of `F_A = s^{3/2}f_A` (source 4993, 2683). -/
theorem affCoef_eq (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) {p : Chart} (hp : 0 < p.1) :
    NearInst.Kflat.affCoef ν μ χf A p = p.1 • merOf (fA ν μ χf A p.1 p.2) := by
  unfold NearInst.Kflat.affCoef FA
  rw [smul_smul, merOf_smul]
  congr 1
  have hs : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp, Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  field_simp

/-- The block of the polarized stress: `nsSym (v⊗b + b⊗v + X) - nsSym (0 + X)` is `v_ib_j + b_iv_j`. -/
theorem block_symOuter (a b : Merid) (X : Ten3) (i j : Fin 2) :
    ((NearInst.nsSym (NearInst.ten3Of (IIIa.symOuter a b) + X) (NearInst.merIdx i)
        (NearInst.merIdx j) : ℝ) : ℂ) -
      ((NearInst.nsSym (0 + X) (NearInst.merIdx i) (NearInst.merIdx j) : ℝ) : ℂ) =
      ((a i : ℝ) : ℂ) * ((b j : ℝ) : ℂ) + ((b i : ℝ) : ℂ) * ((a j : ℝ) : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    simp [NearInst.nsSym, NearInst.symRZ, NearInst.ten3Of, NearInst.merIdx, IIIa.symOuter,
      IIIa.embedMerid] <;> push_cast <;> ring

/-- The forced integrand of `b₀ - b̂` around the train, when the tensor of `b̂` is the polarized
stress of `b₀ - b̂`. -/
theorem forced_split (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (f : Chart → Fin 2 → ℂ) (b₀ bh : Chart → Fin 2 → ℂ) (F : Chart → Fin 2 → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : Chart)
    (hF : ∀ i j, F p i j = (vel p.1 p.2 i : ℂ) * (b₀ p j - bh p j) +
      (b₀ p i - bh p i) * (vel p.1 p.2 j : ℂ)) :
    forcedIntegrand ν μ vel f (fun p i => b₀ p i - bh p i) Φ p =
      forcedIntegrand ν μ (fun _ _ _ => 0) f b₀ Φ p -
        flatIntegrand ν μ (fun _ _ _ => 0) F bh Φ p := by
  simp only [forcedIntegrand, flatIntegrand, Fin.sum_univ_two, hF, Complex.ofReal_zero]
  ring

/-- **(c) The column of the near operators is a forced column** (source 4084-4086, flat form:
`b = R₀f - S₀T₀`, `T₀ = M₀b`; 3420-3440, 1684-1689). -/
theorem operatorColumn_of (h0 : BodyColumnFlat) {c mZ ρb ν μ : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hμ : 0 < μ + 1 / 4) {tr : UnforcedLeray.B0140.TrainSol ν c} (o : NearInst.NearOps c mZ ρb)
    (R0 : Hsp c →L[ℝ] Hsp c) (hM0 : NearInst.IsFlatMult o.M0 tr)
    (hS0 : NearInst.IsFreeStress o.S0 ν μ)
    (hR0 : NearInst.IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ)))
    (h b : Hsp c) (f : Chart → Fin 2 → ℂ)
    (hf : ∀ᵐ p ∂(ageμ c (-3 / 2)), ∀ i, NearInst.velC h p i = (p.1 : ℂ) * f p i)
    (hb : b = R0 h - o.S0 (o.M0 b)) :
    ∃ (b' : Chart → Fin 2 → ℂ) (G' : Chart → Fin 2 → Fin 2 → ℂ),
      b' =ᵐ[ageμ c (-3 / 2)] NearInst.velC b ∧
        IsForcedColumn c ν (μ : ℂ) (trainVel tr) f b' G' := by
  obtain ⟨b₀, G₀, hb₀, hc₀⟩ := h0 c ν μ hc hν hμ R0 hR0 h f hf
  obtain ⟨b₁, G₁, hb₁, hs₁⟩ := hS0 (o.M0 b)
  obtain ⟨b₂, G₂, hb₂, hs₂⟩ := hS0 0
  have hsub := IIIa.causalSolSub c ν (μ : ℂ) (fun _ _ _ => 0) _ _ b₁ b₂ G₁ G₂ hs₁ hs₂
  set bh : Chart → Fin 2 → ℂ := fun p i => b₁ p i - b₂ p i with hbh
  set Gh : Chart → Fin 2 → Fin 2 → ℂ := fun p i j => G₁ p i j - G₂ p i j with hGh
  set Fd : Chart → Fin 2 → Fin 2 → ℂ := fun p i j =>
    NearInst.merBlockC (NearInst.zsum (o.M0 b)) p i j -
      NearInst.merBlockC (NearInst.zsum (0 : Zsp c mZ ρb)) p i j with hFd
  -- the representative of `b`
  have hrep : (fun p i => b₀ p i - bh p i) =ᵐ[ageμ c (-3 / 2)] NearInst.velC b := by
    have hz : ((o.S0 0 : Hsp c) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] 0 := by
      rw [map_zero]
      exact Lp.coeFn_zero _ _ _
    filter_upwards [hb₀, hb₁, hb₂, hz, Lp.coeFn_sub (R0 h) (o.S0 (o.M0 b))] with p h0 h1 h2 h3 h4
    funext i
    have hbp : b p = (R0 h - o.S0 (o.M0 b) : Hsp c) p := by rw [← hb]
    simp only [hbh, h0, h1, h2, h3, NearInst.velC, hbp, h4, Pi.sub_apply, Pi.zero_apply,
      PiLp.sub_apply, PiLp.zero_apply, Complex.ofReal_sub, Complex.ofReal_zero, sub_zero]
  -- the tensor of `b̂` is the polarized stress of `b`
  have hT : ∀ᵐ p ∂((volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)),
      ∀ i j, Fd p i j = ((trainVel tr p.1 p.2 i : ℝ) : ℂ) * (b₀ p j - bh p j) +
        (b₀ p i - bh p i) * ((trainVel tr p.1 p.2 j : ℝ) : ℂ) := by
    have hfst := (volCyl_ac_ageμ hc (-1 / 2)).ae_le
      ((ageμ_ac_z1Measure c mZ).ae_le (hM0 b).1)
    have hzero : (((0 : Zsp c mZ ρb).fst : Z1sp c mZ) : Chart → Ten3) =ᵐ[z1Measure c mZ] 0 := by
      have e : (0 : Zsp c mZ ρb).fst = 0 := rfl
      rw [e]
      exact Lp.coeFn_zero _ _ _
    have hzero' := (volCyl_ac_ageμ hc (-1 / 2)).ae_le ((ageμ_ac_z1Measure c mZ).ae_le hzero)
    have hsnd : (o.M0 b).snd = (0 : Zsp c mZ ρb).snd := by
      rw [(hM0 b).2]
      rfl
    filter_upwards [hfst, hzero', (volCyl_ac_ageμ hc (-3 / 2)).ae_le hrep] with p hp1 hp2 hp3
    intro i j
    have e1 : NearInst.zsum (o.M0 b) p =
        NearInst.ten3Of (IIIa.symOuter (NearInst.trainMer tr p) (b p)) +
          (((0 : Zsp c mZ ρb).snd : HTrho c ρb) : Chart → Ten3) p := by
      simp only [NearInst.zsum, hp1, hsnd]
    have e2 : NearInst.zsum (0 : Zsp c mZ ρb) p =
        0 + (((0 : Zsp c mZ ρb).snd : HTrho c ρb) : Chart → Ten3) p := by
      simp only [NearInst.zsum, hp2, Pi.zero_apply]
    have hbi : ∀ k, b₀ p k - bh p k = ((b p k : ℝ) : ℂ) := fun k => congrFun hp3 k
    simp only [hFd, NearInst.merBlockC, e1, e2, block_symOuter, hbi]
    rfl
  refine ⟨fun p i => b₀ p i - bh p i, fun p i j => G₀ p i j - Gh p i j, hrep, ?_⟩
  have hE := hc₀.toIsEnergyField.sub hsub.toEnergyField
  have hfun : ∀ Φ, forcedIntegrand ν (μ : ℂ) (trainVel tr) f (fun p i => b₀ p i - bh p i) Φ
      =ᵐ[(volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)]
      fun p => forcedIntegrand ν (μ : ℂ) (fun _ _ _ => 0) f b₀ Φ p -
        flatIntegrand ν (μ : ℂ) (fun _ _ _ => 0) Fd bh Φ p := by
    intro Φ
    filter_upwards [hT] with p hp
    exact forced_split ν (μ : ℂ) (trainVel tr) f b₀ bh Fd Φ p hp
  refine ⟨hE, fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
  · exact ((hc₀.integrable Φ hΦ).sub (hsub.integrable Φ hΦ)).congr (hfun Φ).symm
  · rw [integral_congr_ae (hfun Φ), integral_sub (hc₀.integrable Φ hΦ) (hsub.integrable Φ hΦ),
      hc₀.weak Φ hΦ, hsub.weak Φ hΦ, sub_self]

/-! ## (b) The Duhamel column of the setting -/

/-- `ω ψ` is integrable on the cell for `ω ∈ X_{m,c}` and a cylinder test `ψ` (`xFn` is
integrable on the cell, `ψ` is bounded on it). -/
theorem xFn_mul_test_integrableOn {c m : ℝ} [Fact (1 < m)] (x : Xmc c m) {ψ : ℝ × ℝ → ℝ}
    (hψ : B0579.IsCylTest c ψ) :
    IntegrableOn (fun p => xFn x p * (ψ p : ℂ)) (B0579.cell c) := by
  obtain ⟨C, -, hC⟩ := UnforcedLeray.Short.IIb.cylBd_band_bdd hψ
  refine Integrable.mul_bdd (c := C) (xFn_integrableOn x) ?_ ?_
  · exact (Complex.continuous_ofReal.comp hψ.continuous).aestronglyMeasurable
  · refine (ae_restrict_iff' (by exact measurableSet_Ico.prod MeasurableSet.univ)).2 (Eventually.of_forall fun p hp => ?_)
    simpa using hC p hp
/-- **(b) `K_cξ_B` is a forced column with the force `f_A`** (source 4610-4615, 4594-4608). -/
theorem kcColumn_of (hCurl : FlatForceCurl) (hLoc : FlatForceLocal) (hDec : FlatForceDecay)
    (hReg : FlatXiRegular)
    (hEn : KcPathEnergy) (hVort : FlatColumnVorticity) (hVel : VorticityToVelocity)
    {κ : IIIa.PlanarFrameKernels} {ν m : ℝ} [Fact (1 < m)] [Fact (0 < cOf ν)]
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (D : FlatInstData κ ν (cOf ν) m tr)
    (hν : 0 < ν) (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr) {μ as : ℝ} (hμ : 0 < μ)
    {χf : ℝ → ℝ} (hχf : IsSourceCutoffC χf) {A : ℝ → Mat3} (hA : IsAffElem as A) :
    ∃ G : Chart → Fin 2 → Fin 2 → ℂ,
      IsForcedColumn (cOf ν) ν (μ : ℂ) (trainVel tr) (forceC ν μ χf A)
        (kcCol D (μ : ℂ) (Bmat ν μ χf A)) G := by
  have hc : 0 < cOf ν := Fact.out
  obtain ⟨hcont, hbd⟩ := hReg κ ν (cOf ν) m tr D μ as χf A hν hμ hχf hA
  obtain ⟨G, hG⟩ := hEn (cOf ν) m (xiD D (μ : ℂ) (Bmat ν μ χf A)) hcont
    (fun s hs => xiD_nonpos D _ _ hs) hbd
  have hOmInt : ∀ s, 0 < s → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest (cOf ν) ψ →
      IntegrableOn (fun x => xFn (xiD D (μ : ℂ) (Bmat ν μ χf A) s) x * (ψ x : ℂ)) (B0579.cell (cOf ν)) :=
    fun s _ ψ hψ => xFn_mul_test_integrableOn _ hψ
  have hBS : ∀ s, 0 < s → IsBiotSavart (cOf ν) (xFn (xiD D (μ : ℂ) (Bmat ν μ χf A) s))
      (fun x => kcCol D (μ : ℂ) (Bmat ν μ χf A) (s, x)) := fun s _ =>
    isBiotSavart_kc (xiD_real D μ (Bmat ν μ χf A) s)
  have hcurl : ∀ s, 0 < s → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest (cOf ν) ψ →
      ∫ x in B0579.cell (cOf ν), xFn (gBD D (Bmat ν μ χf A) s) x * (ψ x : ℂ) =
        ∫ x in B0579.cell (cOf ν), (forceC ν μ χf A (s, x) 0 * (B0579.pd 1 ψ x : ℂ) -
          forceC ν μ χf A (s, x) 1 * (B0579.pd 0 ψ x : ℂ)) := by
    intro s hs ψ hψ
    obtain ⟨-, heq⟩ := hCurl ν μ χf A s hν hs ψ hψ
    have e1 : ∫ x in B0579.cell (cOf ν), xFn (gBD D (Bmat ν μ χf A) s) x * (ψ x : ℂ) =
        ∫ x in B0579.cell (cOf ν), gBProf ν (cOf ν) s (Bmat ν μ χf A s) x * (ψ x : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [xFn_gBD D (Bmat ν μ χf A) s] with x hx
      rw [hx]
    have e2 : ∫ x in B0579.cell (cOf ν), (forceC ν μ χf A (s, x) 0 * (B0579.pd 1 ψ x : ℂ) -
          forceC ν μ χf A (s, x) 1 * (B0579.pd 0 ψ x : ℂ)) =
        ((∫ x in B0579.cell (cOf ν), (merOf (fA ν μ χf A s x) 0 * B0579.pd 1 ψ x -
          merOf (fA ν μ χf A s x) 1 * B0579.pd 0 ψ x) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [forceC, NearInst.velC]
      push_cast
      ring
    rw [e1, e2, heq]
  refine ⟨G, { hG with
    integrable := fun Φ hΦ => (hVel ν (cOf ν) μ tr (fun s => xFn (xiD D (μ : ℂ) (Bmat ν μ χf A) s))
      (fun s => xFn (gBD D (Bmat ν μ χf A) s)) (kcCol D (μ : ℂ) (Bmat ν μ χf A)) G
      (forceC ν μ χf A) hν hc htr hG hBS (forceC_memLp_band hLoc hDec hν hχf hA) hcurl
      (fun φ hφ s hs => hVort κ ν (cOf ν) m tr D μ as χf A hν hμ hχf hA φ hφ s hs) hOmInt Φ hΦ).1
    weak := fun Φ hΦ => (hVel ν (cOf ν) μ tr (fun s => xFn (xiD D (μ : ℂ) (Bmat ν μ χf A) s))
      (fun s => xFn (gBD D (Bmat ν μ χf A) s)) (kcCol D (μ : ℂ) (Bmat ν μ χf A)) G
      (forceC ν μ χf A) hν hc htr hG hBS (forceC_memLp_band hLoc hDec hν hχf hA) hcurl
      (fun φ hφ s hs => hVort κ ν (cOf ν) m tr D μ as χf A hν hμ hχf hA φ hφ s hs) hOmInt Φ hΦ).2 }⟩

/-! ## The pin -/

/-- **(e) The readout of the setting** (source 4610-4612): `𝔗A = M_B = v⊗K_cξ_B + K_cξ_B⊗v`. -/
theorem frakT_actual {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (D : FlatInstData κ ν c m tr) (χo : ℝ → ℝ) (ε μ : ℝ)
    (χf : ℝ → ℝ) (A : ℝ → Mat3) (p : Chart) :
    frakT (actualFlatSetting D χo ε) ν μ χf A p =
      IIIa.symOuter (NearInst.trainMer tr p) (kcMer (xiD D (μ : ℂ) (Bmat ν μ χf A) p.1) p.2) :=
  rfl

/-- **`IsFlatDuhamelColumn` for the concrete flat setting** (source 4761-4763, 4596-4612,
4084-4086, 3420-3446): from the leaves (a)-(c), uniqueness (d) at the regime, and the readout (e). -/
theorem isFlatDuhamelColumn_of (hCurl : FlatForceCurl) (hLoc : FlatForceLocal)
    (hDec : FlatForceDecay) (hReg : FlatXiRegular) (hEn : KcPathEnergy) (hVort : FlatColumnVorticity)
    (hVel : VorticityToVelocity) (hBody : BodyColumnFlat)
    {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (D : FlatInstData κ ν c m tr) (χo : ℝ → ℝ) (ε : ℝ)
    (hc : 0 < c) (hν : 0 < ν) (hcν : c = cOf ν) (htr : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {μ : ℝ} (hμ : 0 < μ) (hU : FlatHomogeneousUnique c ν (μ : ℂ) (trainVel tr)) (as : ℝ)
    (χf : ℝ → ℝ) :
    NearInst.Kflat.IsFlatDuhamelColumn (actualFlatSetting D χo ε) hc tr μ as χf := by
  subst hcν
  intro hχf mZ ρb o R0 hM0 hS0 hR0 _ A hA h b hh hb
  have hf : ∀ᵐ p ∂(ageμ (cOf ν) (-3 / 2)), ∀ i,
      NearInst.velC h p i = (p.1 : ℂ) * forceC ν μ χf A p i := by
    filter_upwards [hh, ae_ageμ_pos (cOf ν) (-3 / 2)] with p hp hpos i
    have e : (h : Chart → Merid) p = p.1 • merOf (fA ν μ χf A p.1 p.2) := by
      rw [hp, affCoef_eq ν μ χf A hpos]
    simp only [NearInst.velC, forceC, e, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  obtain ⟨b₂, G₂, hb₂, hcol₂⟩ :=
    operatorColumn_of hBody hc hν (by linarith) o R0 hM0 hS0 hR0 h b _ hf hb
  obtain ⟨G₁, hcol₁⟩ := kcColumn_of hCurl hLoc hDec hReg hEn hVort hVel D hν htr hμ hχf hA
  have hu := forcedColumn_unique hU hcol₁ hcol₂
  have h1 := (oldMeasure_ac_volCyl hν).ae_le hu
  have h2 := ((oldMeasure_ac_volCyl hν).trans (volCyl_ac_ageμ hc (-3 / 2))).ae_le hb₂
  filter_upwards [h1, h2] with p hp1 hp2
  rw [frakT_actual]
  congr 1
  ext i
  have h3 := congrFun (hp1.trans hp2) i
  simp only [kcCol, NearInst.velC, Complex.ofReal_inj] at h3
  exact h3

/-! ## (d) Uniqueness from `PolyCausal` and the pin at small viscosity -/

theorem cOf_eq_rpow {ν : ℝ} (hν : 0 < ν) : cOf ν = ν ^ (-2 : ℝ) := by
  rw [cOf, Real.rpow_neg hν.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem cOf_pos {ν : ℝ} (hν : 0 < ν) : 0 < cOf ν := by
  unfold cOf
  positivity

/-- **(d) Uniqueness of homogeneous causal solutions from `prop:short-polynomial-causal`**
(source 3426-3446: "there is a unique causal zero-entrance energy solution"): the zero field is a
solution, so every homogeneous solution vanishes. -/
theorem flatHomogeneousUnique_of_polyCausal (hPC : IIIa.PolyCausal) {P : PlanarData}
    (hP : IsPlanarReference P) {Kset : Set ℝ} (hK : IsCompact Kset)
    (hKs : Kset ⊆ Ioo 0 (1 / 4)) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ c : ℝ, c = cOf ν →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ μ ∈ Kset, FlatHomogeneousUnique c ν (μ : ℂ) (trainVel tr) := by
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Kset with hKdef
  have hK' : IIIa.IsAdmissibleK K := by
    refine ⟨hK.image Complex.continuous_ofReal, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨by simpa using (hKs hx).1, by simpa using (hKs hx).2⟩
  obtain ⟨M, C, ν₀, hν₀, hpc⟩ := hPC P hP K hK'
  refine ⟨ν₀, hν₀, fun ν hν c hc tr htr μ hμ => ?_⟩
  have hc' : c = ν ^ (-2 : ℝ) := by rw [hc, cOf_eq_rpow hν.1]
  subst hc'
  intro b G hsol
  have hfin : IIIa.tCalNorm (ν ^ (-2 : ℝ))
      (IIIa.gainConj P.eigenvalue.re ν (fun _ _ _ => (0 : ℂ))) < ⊤ := by
    simp [IIIa.tCalNorm, IIIa.gainConj, IIIa.tnorm2]
  obtain ⟨b₀, G₀, -, -, huniq⟩ := hpc ν hν tr htr (μ : ℂ) ⟨μ, hμ, rfl⟩ (fun _ _ _ => 0)
    (fun _ _ _ => rfl) (fun _ _ => measurable_const) hfin
  have e1 := huniq b G hsol
  have e2 := huniq _ _ (isCausal_zero (ν ^ (-2 : ℝ)) ν (μ : ℂ) (trainVel tr))
  filter_upwards [e1, e2] with p h1 h2
  rw [h1, ← h2]
  rfl

/-- **The pin `IsFlatDuhamelColumn` for the concrete flat setting at every small viscosity**
(source 4761-4763, 4596-4612, 3426-3446), from the leaves and `PolyCausal`. -/
theorem isFlatDuhamelColumn_of_leaves (hCurl : FlatForceCurl) (hLoc : FlatForceLocal)
    (hDec : FlatForceDecay) (hReg : FlatXiRegular) (hEn : KcPathEnergy) (hVort : FlatColumnVorticity)
    (hVel : VorticityToVelocity) (hBody : BodyColumnFlat) (hPC : IIIa.PolyCausal)
    {P : PlanarData} (hP : IsPlanarReference P) {Kset : Set ℝ} (hK : IsCompact Kset)
    (hKs : Kset ⊆ Ioo 0 (1 / 4)) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ (m : ℝ) [Fact (1 < m)] [Fact (0 < cOf ν)]
      (κ : IIIa.PlanarFrameKernels) (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ (D : FlatInstData κ ν (cOf ν) m tr) (χo : ℝ → ℝ) (ε : ℝ) (hc : 0 < cOf ν),
        ∀ μ ∈ Kset, ∀ (as : ℝ) (χf : ℝ → ℝ),
          NearInst.Kflat.IsFlatDuhamelColumn (actualFlatSetting D χo ε) hc tr μ as χf := by
  obtain ⟨ν₀, hν₀, hU⟩ := flatHomogeneousUnique_of_polyCausal hPC hP hK hKs
  refine ⟨ν₀, hν₀, fun ν hν m _ _ κ tr htr D χo ε hc μ hμ as χf => ?_⟩
  exact isFlatDuhamelColumn_of hCurl hLoc hDec hReg hEn hVort hVel hBody D χo ε hc hν.1 rfl htr
    (hKs hμ).1 (hU ν hν (cOf ν) rfl tr htr μ hμ) as χf

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
