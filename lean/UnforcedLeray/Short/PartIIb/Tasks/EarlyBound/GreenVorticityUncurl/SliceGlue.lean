import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.GreenVorticityUncurl.Needed
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice.PeriodizeTest
import UnforcedLeray.Infra.JointMeasurableRep

/-!
# `PartII-b:F6/2/1`: Jointly measurable `c`-periodic Biot–Savart slice glue (`SliceBiotSavartGlue`)

Source of record: `the November 2 reference manuscript` (SP), lines 2258–2268.

Proves `UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded.sliceBiotSavartGlue_proof`:
given a continuous zero-circulation trajectory `ω : ℝ → Xmc c m` (`8 < m`, `1 ≤ c`, `0 < H`) on
`Icc 0 H`, lifts the canonical cylinder Biot–Savart triple
`(B0583.velocity, B0583.velGradQ, B0583.velGradEta)` to jointly strongly measurable, `c`-periodic
profiles `z, zq, zη : CProf` on `Coord` satisfying `HasWeakVec vQ0 dZero z zq`,
`HasWeakVec vEta dZero z zη`, weak solenoidality on `Ioo 0 H ×ˢ univ`, and slicewise a.e.
agreement on `B0579.cell c` at every `s ∈ Ioc 0 H`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb.GreenVorticityUncurlSliceGlueAux

open UnforcedLeray.Short.IIb

/-! ### 1. Subtraction linearity of canonical `B0583` Biot–Savart operators -/

private lemma integral_sub_eq_zero_of_X {c m : ℝ} (hm : 1 ≤ m) {ω₁ ω₂ : B0579.X c m}
    (h₁ : ∫ x in B0579.cell c, ω₁ x = 0) (h₂ : ∫ x in B0579.cell c, ω₂ x = 0) :
    ∫ x in B0579.cell c, ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) x = 0 := by
  have hae : ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) =ᵐ[B0581.cellVol c]
      fun x => ω₁ x - ω₂ x :=
    (B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_sub ω₁ ω₂)
  have hi₁ : Integrable (ω₁ : B0579.Plane → ℝ) (B0581.cellVol c) := B0583.integrable_of_X hm ω₁
  have hi₂ : Integrable (ω₂ : B0579.Plane → ℝ) (B0581.cellVol c) := B0583.integrable_of_X hm ω₂
  change ∫ x, ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) x ∂B0581.cellVol c = 0
  rw [integral_congr_ae hae, integral_sub hi₁ hi₂]
  change (∫ x in B0579.cell c, ω₁ x) - (∫ x in B0579.cell c, ω₂ x) = 0
  rw [h₁, h₂, sub_zero]

private lemma ofX_sub (c m : ℝ) (hm0 : 0 ≤ m) (ω₁ ω₂ : B0579.X c m) :
    B0581.ofX c m hm0 (ω₁ - ω₂) = B0581.ofX c m hm0 ω₁ - B0581.ofX c m hm0 ω₂ := by
  rw [Lp.ext_iff]
  have hae : ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) =ᵐ[B0581.cellVol c]
      fun x => ω₁ x - ω₂ x :=
    (B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_sub ω₁ ω₂)
  filter_upwards [B0581.coeFn_ofX c m hm0 (ω₁ - ω₂), B0581.coeFn_ofX c m hm0 ω₁,
    B0581.coeFn_ofX c m hm0 ω₂, Lp.coeFn_sub (B0581.ofX c m hm0 ω₁) (B0581.ofX c m hm0 ω₂),
    hae] with x h12 h1 h2 hsub hx
  rw [h12, hsub, Pi.sub_apply, h1, h2, hx, Complex.ofReal_sub]

private lemma nonzeroPart_sub (c : ℝ) [Fact (0 < c)] (a b : Lp ℂ 2 (B0581.cellVol c)) :
    B0581.nonzeroPart c (a - b) = B0581.nonzeroPart c a - B0581.nonzeroPart c b := by
  simp only [B0581.nonzeroPart, B0581.meanPart, map_sub, lp.coeFn_sub, Pi.sub_apply]
  abel

private lemma omegaBar_sub_ae {c m : ℝ} (hm : 1 ≤ m) (ω₁ ω₂ : B0579.X c m) :
    B0583.omegaBar c ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) =ᵐ[volume]
      fun η => B0583.omegaBar c ω₁ η - B0583.omegaBar c ω₂ η := by
  have hae : ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) =ᵐ[(B0581.μq c).prod volume]
      fun x => ω₁ x - ω₂ x := by
    rw [← B0581.cellVol_eq]
    exact (B0579.ac_cellMeasure c m).ae_le (Lp.coeFn_sub ω₁ ω₂)
  have hswap : ∀ᵐ z : ℝ × ℝ ∂(volume : Measure ℝ).prod (B0581.μq c),
      ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) z.swap = ω₁ z.swap - ω₂ z.swap :=
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := B0581.μq c)).quasiMeasurePreserving.ae hae
  have hi₁ : Integrable (ω₁ : B0579.Plane → ℝ) ((B0581.μq c).prod volume) := by
    rw [← B0581.cellVol_eq]; exact B0583.integrable_of_X hm ω₁
  have hi₂ : Integrable (ω₂ : B0579.Plane → ℝ) ((B0581.μq c).prod volume) := by
    rw [← B0581.cellVol_eq]; exact B0583.integrable_of_X hm ω₂
  filter_upwards [Measure.ae_ae_of_ae_prod hswap, hi₁.prod_left_ae, hi₂.prod_left_ae]
    with η hη hq₁ hq₂
  have hcongr : ∫ q in B0581.qInt c, ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) (q, η) =
      ∫ q in B0581.qInt c, (ω₁ (q, η) - ω₂ (q, η)) :=
    integral_congr_ae hη
  simp only [B0583.omegaBar, hcongr, integral_sub hq₁ hq₂, mul_sub]

private lemma zeroVelLp_sub (c : ℝ) [hc : Fact (0 < c)] {m : ℝ} (hm : 1 ≤ m)
    {ω₁ ω₂ : B0579.X c m}
    (h₁ : ∫ x in B0579.cell c, ω₁ x = 0) (h₂ : ∫ x in B0579.cell c, ω₂ x = 0)
    (h₁₂ : ∫ x in B0579.cell c, ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) x = 0) :
    B0583.zeroVelLp c hm (ω₁ - ω₂) h₁₂ =
      B0583.zeroVelLp c hm ω₁ h₁ - B0583.zeroVelLp c hm ω₂ h₂ := by
  have hob := omegaBar_sub_ae hm ω₁ ω₂
  have hi₁ := (B0583.zeroMode_facts hc.out hm ω₁ h₁).1
  have hi₂ := (B0583.zeroMode_facts hc.out hm ω₂ h₂).1
  have hprim : ∀ η : ℝ,
      B0582.zeroModePrimitive (B0583.omegaBar c (ω₁ - ω₂ : B0579.X c m)) η =
        B0582.zeroModePrimitive (B0583.omegaBar c ω₁) η -
          B0582.zeroModePrimitive (B0583.omegaBar c ω₂) η := by
    intro η
    unfold B0582.zeroModePrimitive
    rw [integral_congr_ae (ae_restrict_of_ae hob),
      integral_sub hi₁.integrableOn hi₂.integrableOn]
  rw [Lp.ext_iff]
  filter_upwards [B0583.coeFn_zeroVelLp c hm (ω₁ - ω₂) h₁₂,
    B0583.coeFn_zeroVelLp c hm ω₁ h₁, B0583.coeFn_zeroVelLp c hm ω₂ h₂,
    Lp.coeFn_sub (B0583.zeroVelLp c hm ω₁ h₁) (B0583.zeroVelLp c hm ω₂ h₂)]
    with x hx12 hx1 hx2 hsub
  rw [hx12, hsub, Pi.sub_apply, hx1, hx2]
  ext j
  simp only [B0583.zeroVel, B0583.profField, hprim x.2, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  push_cast
  ring

private lemma zeroVelEtaLp_sub (c : ℝ) [hc : Fact (0 < c)] {m : ℝ} (hm : 1 ≤ m)
    {ω₁ ω₂ : B0579.X c m}
    (h₁ : ∫ x in B0579.cell c, ω₁ x = 0) (h₂ : ∫ x in B0579.cell c, ω₂ x = 0)
    (h₁₂ : ∫ x in B0579.cell c, ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) x = 0) :
    B0583.zeroVelEtaLp c hm (ω₁ - ω₂) h₁₂ =
      B0583.zeroVelEtaLp c hm ω₁ h₁ - B0583.zeroVelEtaLp c hm ω₂ h₂ := by
  have hob_cell : ∀ᵐ x : B0579.Plane ∂B0581.cellVol c,
      B0583.omegaBar c (ω₁ - ω₂ : B0579.X c m) x.2 =
        B0583.omegaBar c ω₁ x.2 - B0583.omegaBar c ω₂ x.2 := by
    rw [B0581.cellVol_eq]
    exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd
      (omegaBar_sub_ae hm ω₁ ω₂)
  rw [Lp.ext_iff]
  filter_upwards [B0583.coeFn_zeroVelEtaLp c hm (ω₁ - ω₂) h₁₂,
    B0583.coeFn_zeroVelEtaLp c hm ω₁ h₁, B0583.coeFn_zeroVelEtaLp c hm ω₂ h₂,
    Lp.coeFn_sub (B0583.zeroVelEtaLp c hm ω₁ h₁) (B0583.zeroVelEtaLp c hm ω₂ h₂),
    hob_cell] with x hx12 hx1 hx2 hsub hobx
  rw [hx12, hsub, Pi.sub_apply, hx1, hx2]
  ext j
  simp only [B0583.zeroVelEta, B0583.profField, hobx, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  push_cast
  ring

private lemma velocity_sub (c : ℝ) [Fact (0 < c)] {m : ℝ} (hm : 1 ≤ m)
    {ω₁ ω₂ : B0579.X c m}
    (h₁ : ∫ x in B0579.cell c, ω₁ x = 0) (h₂ : ∫ x in B0579.cell c, ω₂ x = 0)
    (h₁₂ : ∫ x in B0579.cell c, ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) x = 0) :
    B0583.velocity c hm (ω₁ - ω₂) h₁₂ =
      B0583.velocity c hm ω₁ h₁ - B0583.velocity c hm ω₂ h₂ := by
  simp only [B0583.velocity, ofX_sub, nonzeroPart_sub, map_sub, zeroVelLp_sub c hm h₁ h₂ h₁₂]
  abel

private lemma velGradQ_sub (c : ℝ) [Fact (0 < c)] {m : ℝ} (hm : 1 ≤ m)
    (ω₁ ω₂ : B0579.X c m) :
    B0583.velGradQ c hm (ω₁ - ω₂) = B0583.velGradQ c hm ω₁ - B0583.velGradQ c hm ω₂ := by
  simp only [B0583.velGradQ, ofX_sub, nonzeroPart_sub, map_sub]

private lemma velGradEta_sub (c : ℝ) [Fact (0 < c)] {m : ℝ} (hm : 1 ≤ m)
    {ω₁ ω₂ : B0579.X c m}
    (h₁ : ∫ x in B0579.cell c, ω₁ x = 0) (h₂ : ∫ x in B0579.cell c, ω₂ x = 0)
    (h₁₂ : ∫ x in B0579.cell c, ((ω₁ - ω₂ : B0579.X c m) : B0579.Plane → ℝ) x = 0) :
    B0583.velGradEta c hm (ω₁ - ω₂) h₁₂ =
      B0583.velGradEta c hm ω₁ h₁ - B0583.velGradEta c hm ω₂ h₂ := by
  simp only [B0583.velGradEta, ofX_sub, nonzeroPart_sub, map_sub,
    zeroVelEtaLp_sub c hm h₁ h₂ h₁₂]
  abel

/-! ### 2. Continuity on `Icc 0 H` from Lipschitz norm bounds -/

private lemma continuousOn_of_norm_sub_le {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {S : Set ℝ} {ω : ℝ → E} (hω : ContinuousOn ω S)
    {g : ℝ → F} {L : ℝ} (hL : 0 < L)
    (hlip : ∀ s₁ ∈ S, ∀ s₂ ∈ S, ‖g s₁ - g s₂‖ ≤ L * ‖ω s₁ - ω s₂‖) :
    ContinuousOn g S := by
  rw [Metric.continuousOn_iff] at hω ⊢
  intro s₁ hs₁ ε hε
  obtain ⟨δ, hδ, hωδ⟩ := hω s₁ hs₁ (ε / L) (div_pos hε hL)
  refine ⟨δ, hδ, fun s₂ hs₂ hdist => ?_⟩
  rw [dist_eq_norm]
  calc ‖g s₂ - g s₁‖
      ≤ L * ‖ω s₂ - ω s₁‖ := hlip s₂ hs₂ s₁ hs₁
    _ = L * dist (ω s₂) (ω s₁) := by rw [dist_eq_norm]
    _ < L * (ε / L) := mul_lt_mul_of_pos_left (hωδ s₂ hs₂ hdist) hL
    _ = ε := mul_div_cancel₀ ε hL.ne'

/-! ### 3. `c`-periodic folding in `q` and truncation to `Ioc 0 H` -/

private def foldQ (c q : ℝ) : ℝ :=
  q - (Int.floor ((q + c / 2) / c) : ℝ) * c

private def foldCoord (c : ℝ) (x : Coord) : Coord :=
  (x.1, (foldQ c x.2.1, x.2.2))

private def cPeriodicLift (c H : ℝ) (F : ℝ × B0579.Plane → B0581.Vel) (x : Coord) : CMerid :=
  if x.1 ∈ Ioc 0 H then F (foldCoord c x) else 0

private lemma measurable_foldCoord (c : ℝ) : Measurable (foldCoord c) := by
  have hm_fl : Measurable (fun q : ℝ => (Int.floor ((q + c / 2) / c) : ℝ)) :=
    (measurable_from_top : Measurable (Int.cast : ℤ → ℝ)).comp
      (Int.measurable_floor.comp ((measurable_id.add_const (c / 2)).div_const c))
  have hm_q : Measurable (foldQ c) :=
    measurable_id.sub (hm_fl.mul_const c)
  exact measurable_fst.prodMk
    ((hm_q.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

private lemma stronglyMeasurable_cPeriodicLift (c H : ℝ) {F : ℝ × B0579.Plane → B0581.Vel}
    (hF : StronglyMeasurable F) :
    StronglyMeasurable (cPeriodicLift c H F) :=
  (hF.comp_measurable (measurable_foldCoord c)).ite
    (measurableSet_Ioc.preimage measurable_fst) stronglyMeasurable_const

private lemma foldQ_add_period {c : ℝ} (hc : 0 < c) (q : ℝ) :
    foldQ c (q + c) = foldQ c q := by
  unfold foldQ
  have hdiv : (q + c + c / 2) / c = (q + c / 2) / c + 1 := by
    field_simp [hc.ne']
    ring
  rw [hdiv, Int.floor_add_one]
  push_cast
  ring

private lemma qPeriodic_cPeriodicLift {c H : ℝ} (hc : 0 < c)
    (F : ℝ × B0579.Plane → B0581.Vel) :
    QPeriodic c (cPeriodicLift c H F) := by
  refine Eventually.of_forall fun x => ?_
  simp only [cPeriodicLift, qShift, foldCoord, foldQ_add_period hc]

private lemma foldQ_of_mem_cell {c : ℝ} (hc : 0 < c) {p : B0579.Plane} (hp : p ∈ B0579.cell c) :
    foldQ c p.1 = p.1 := by
  have h1 : -(c / 2) ≤ p.1 := hp.1.1
  have h2 : p.1 < c / 2 := hp.1.2
  have hfl : Int.floor ((p.1 + c / 2) / c) = 0 := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · simp only [Int.cast_zero]
      exact div_nonneg (by linarith) hc.le
    · simp only [Int.cast_zero, zero_add, div_lt_one hc]
      linarith
  simp [foldQ, hfl]

private lemma cPeriodicLift_eq_on_cell {c H : ℝ} (hc : 0 < c)
    (F : ℝ × B0579.Plane → B0581.Vel) {s : ℝ} (hs : s ∈ Ioc 0 H)
    {p : B0579.Plane} (hp : p ∈ B0579.cell c) :
    cPeriodicLift c H F (s, p) = F (s, p) := by
  simp only [cPeriodicLift, hs, ↓reduceIte, foldCoord, foldQ_of_mem_cell hc hp, Prod.mk.eta]

private lemma cPeriodicLift_eq_zero_of_notMem (c H : ℝ)
    (F : ℝ × B0579.Plane → B0581.Vel) {s : ℝ} (hs : s ∉ Ioc 0 H) (p : B0579.Plane) :
    cPeriodicLift c H F (s, p) = 0 := by
  simp [cPeriodicLift, hs]

/-! ### 4. Weak derivative congruence, Fubini slices, and uniform `L²(cell)` finiteness -/

private lemma hasWeakCellDerivC_zero (c : ℝ) (k : Fin 2) :
    IIIa.HasWeakCellDerivC c k 0 0 :=
  ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩

private lemma hasWeakCellDerivC_congr_ae {c : ℝ} {k : Fin 2} {φ₁ φ₂ g₁ g₂ : ℝ × ℝ → ℂ}
    (hφ : φ₁ =ᵐ[volume.restrict (B0579.cell c)] φ₂)
    (hg : g₁ =ᵐ[volume.restrict (B0579.cell c)] g₂)
    (h₁ : IIIa.HasWeakCellDerivC c k φ₁ g₁) :
    IIIa.HasWeakCellDerivC c k φ₂ g₂ := by
  refine ⟨fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have hae1 : (fun x => φ₁ x * (B0579.pd k ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => φ₂ x * (B0579.pd k ψ x : ℂ)) := hφ.mono fun x hx => by dsimp; rw [hx]
    have hae2 : (fun x => g₁ x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => g₂ x * (ψ x : ℂ)) := hg.mono fun x hx => by dsimp; rw [hx]
    exact ⟨(h₁.1 ψ hψ).1.congr hae1, (h₁.1 ψ hψ).2.congr hae2⟩
  · have hae1 : (fun x => φ₁ x * (B0579.pd k ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => φ₂ x * (B0579.pd k ψ x : ℂ)) := hφ.mono fun x hx => by dsimp; rw [hx]
    have hae2 : (fun x => g₁ x * (ψ x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        (fun x => g₂ x * (ψ x : ℂ)) := hg.mono fun x hx => by dsimp; rw [hx]
    rw [← integral_congr_ae hae1, ← integral_congr_ae hae2]
    exact h₁.2 ψ hψ

private lemma eLpNorm_coe_Lp_eq {E : Type*} [NormedAddCommGroup E] {μ : Measure B0579.Plane}
    (f : Lp E 2 μ) :
    eLpNorm (f : B0579.Plane → E) 2 μ = ENNReal.ofReal ‖f‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]

private lemma eLpNorm_comp_le_merid (c : ℝ) (g : CProf) (s : ℝ) (i : Fin 2) :
    eLpNorm (fun z => g (s, z) i) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun z => g (s, z)) 2 (volume.restrict (B0579.cell c)) := by
  refine eLpNorm_mono_enorm fun z => ?_
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  exact_mod_cast PiLp.norm_apply_le (g (s, z)) i

private lemma lintegral_Icc_const_lt_top (a b K : ℝ) :
    (∫⁻ _s in Icc a b, ENNReal.ofReal K) < ⊤ := by
  rw [setLIntegral_const, Real.volume_Icc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

private lemma fubini_cell_slices {c a b : ℝ} {F : Coord → ℂ}
    (hF : IntegrableOn F (Icc a b ×ˢ B0579.cell c) volume) :
    IntegrableOn (fun s : ℝ => ∫ z in B0579.cell c, F (s, z)) (Icc a b) volume ∧
      ∀ᵐ s ∂(volume.restrict (Icc a b)),
        IntegrableOn (fun z : B0579.Plane => F (s, z)) (B0579.cell c) volume := by
  have hF' : Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (B0579.cell c))) := by
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact ⟨hF'.integral_prod_left, hF'.prod_right_ae⟩

end UnforcedLeray.Short.IIb.GreenVorticityUncurlSliceGlueAux

namespace UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded

open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.IIb.GreenVorticityUncurlSliceGlueAux

/-- **Proof of `SliceBiotSavartGlue` (`PartII-b:F6/2/1`, SP 2258–2268)**:
lifts the canonical cylinder Biot–Savart triple `(B0583.velocity, velGradQ, velGradEta)` along a
continuous zero-circulation trajectory `ω : ℝ → Xmc c m` on `Icc 0 H` via
`Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn` and `c`-periodic `q`-folding
to jointly strongly measurable, `c`-periodic profiles `z, zq, zη : CProf` on `Coord`. -/
theorem sliceBiotSavartGlue_proof :
    UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded.SliceBiotSavartGlue := by
  intro m hm c H hc1 hH ω hω_cont hω_circ
  have hc0 : 0 < c := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hm_gt1 : (1 : ℝ) < m := by linarith
  have : Fact (0 < c) := ⟨hc0⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  -- Total paths into `Lp B0581.Vel 2 (B0581.cellVol c)`
  let uPath : ℝ → Lp B0581.Vel 2 (B0581.cellVol c) := fun s =>
    if hs : s ∈ Icc 0 H then B0583.velocity c hm1 (ω s) (hω_circ s hs).2 else 0
  let uqPath : ℝ → Lp B0581.Vel 2 (B0581.cellVol c) := fun s =>
    B0583.velGradQ c hm1 (ω s)
  let uηPath : ℝ → Lp B0581.Vel 2 (B0581.cellVol c) := fun s =>
    if hs : s ∈ Icc 0 H then B0583.velGradEta c hm1 (ω s) (hω_circ s hs).2 else 0
  -- Step 1: `ContinuousOn` on `Icc 0 H`
  have hCu_pos : 0 < c / (2 * Real.pi) + 2 := by positivity
  have hu_cont : ContinuousOn uPath (Icc 0 H) := by
    refine continuousOn_of_norm_sub_le hω_cont hCu_pos fun s₁ hs₁ s₂ hs₂ => ?_
    simp only [uPath, hs₁, hs₂, ↓reduceDIte]
    have h₁₂ := integral_sub_eq_zero_of_X hm1 (hω_circ s₁ hs₁).2 (hω_circ s₂ hs₂).2
    rw [← velocity_sub c hm1 (hω_circ s₁ hs₁).2 (hω_circ s₂ hs₂).2 h₁₂]
    exact B0583.norm_velocity_le c hm1 (ω s₁ - ω s₂) h₁₂
  have huq_cont : ContinuousOn uqPath (Icc 0 H) := by
    refine continuousOn_of_norm_sub_le hω_cont one_pos fun s₁ hs₁ s₂ hs₂ => ?_
    simp only [uqPath, one_mul, ← velGradQ_sub c hm1 (ω s₁) (ω s₂)]
    exact B0583.norm_velGradQ_le c hm1 (ω s₁ - ω s₂)
  have huη_cont : ContinuousOn uηPath (Icc 0 H) := by
    refine continuousOn_of_norm_sub_le hω_cont two_pos fun s₁ hs₁ s₂ hs₂ => ?_
    simp only [uηPath, hs₁, hs₂, ↓reduceDIte]
    have h₁₂ := integral_sub_eq_zero_of_X hm1 (hω_circ s₁ hs₁).2 (hω_circ s₂ hs₂).2
    rw [← velGradEta_sub c hm1 (hω_circ s₁ hs₁).2 (hω_circ s₂ hs₂).2 h₁₂]
    exact B0583.norm_velGradEta_le c hm1 (ω s₁ - ω s₂) h₁₂
  -- Step 2: Jointly strongly measurable cell representatives on `Ioc 0 H` and `c`-periodic lifts
  obtain ⟨Fu, hFu_sm, hFu_rep⟩ :=
    Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      measurableSet_Ioc (hu_cont.mono Ioc_subset_Icc_self)
  obtain ⟨Fuq, hFuq_sm, hFuq_rep⟩ :=
    Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      measurableSet_Ioc (huq_cont.mono Ioc_subset_Icc_self)
  obtain ⟨Fuη, hFuη_sm, hFuη_rep⟩ :=
    Infra.JointMeasurableRep.exists_stronglyMeasurable_rep_of_continuousOn
      measurableSet_Ioc (huη_cont.mono Ioc_subset_Icc_self)
  let z : CProf := cPeriodicLift c H Fu
  let zq : CProf := cPeriodicLift c H Fuq
  let zη : CProf := cPeriodicLift c H Fuη
  have hz_sm : StronglyMeasurable z := stronglyMeasurable_cPeriodicLift c H hFu_sm
  have hzq_sm : StronglyMeasurable zq := stronglyMeasurable_cPeriodicLift c H hFuq_sm
  have hzη_sm : StronglyMeasurable zη := stronglyMeasurable_cPeriodicLift c H hFuη_sm
  have hz_per : QPeriodic c z := qPeriodic_cPeriodicLift hc0 Fu
  have hzq_per : QPeriodic c zq := qPeriodic_cPeriodicLift hc0 Fuq
  have hzη_per : QPeriodic c zη := qPeriodic_cPeriodicLift hc0 Fuη
  -- Slicewise a.e. agreement on `B0579.cell c` at every `s ∈ Ioc 0 H`
  have hz_slice : ∀ s : ℝ, ∀ hs : s ∈ Ioc 0 H,
      (fun x => z (s, x)) =ᵐ[volume.restrict (B0579.cell c)]
        (B0583.velocity c hm1 (ω s) (hω_circ s ⟨hs.1.le, hs.2⟩).2 :
          B0579.Plane → B0581.Vel) := by
    intro s hs
    have hcell : (fun x => z (s, x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => Fu (s, x)) :=
      ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun p hp =>
        cPeriodicLift_eq_on_cell hc0 Fu hs hp
    have hrep := hFu_rep s hs
    simp only [uPath, show s ∈ Icc 0 H from ⟨hs.1.le, hs.2⟩, ↓reduceDIte] at hrep
    exact hcell.trans hrep
  have hzq_slice : ∀ s : ℝ, ∀ hs : s ∈ Ioc 0 H,
      (fun x => zq (s, x)) =ᵐ[volume.restrict (B0579.cell c)]
        (B0583.velGradQ c hm1 (ω s) : B0579.Plane → B0581.Vel) := by
    intro s hs
    have hcell : (fun x => zq (s, x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => Fuq (s, x)) :=
      ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun p hp =>
        cPeriodicLift_eq_on_cell hc0 Fuq hs hp
    exact hcell.trans (hFuq_rep s hs)
  have hzη_slice : ∀ s : ℝ, ∀ hs : s ∈ Ioc 0 H,
      (fun x => zη (s, x)) =ᵐ[volume.restrict (B0579.cell c)]
        (B0583.velGradEta c hm1 (ω s) (hω_circ s ⟨hs.1.le, hs.2⟩).2 :
          B0579.Plane → B0581.Vel) := by
    intro s hs
    have hcell : (fun x => zη (s, x)) =ᵐ[volume.restrict (B0579.cell c)] (fun x => Fuη (s, x)) :=
      ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun p hp =>
        cPeriodicLift_eq_on_cell hc0 Fuη hs hp
    have hrep := hFuη_rep s hs
    simp only [uηPath, show s ∈ Icc 0 H from ⟨hs.1.le, hs.2⟩, ↓reduceDIte] at hrep
    exact hcell.trans hrep
  -- Uniform bound on `‖ω s‖` over compact `Icc 0 H`, hence uniform slice `L²(cell)` bounds on `ℝ`
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hω_cont
  let M : ℝ := max 0 M₀
  have hM_nonneg : 0 ≤ M := le_max_left 0 M₀
  have hω_bdd : ∀ s ∈ Icc 0 H, ‖ω s‖ ≤ M := fun s hs => (hM₀ s hs).trans (le_max_right 0 M₀)
  have hz_eLp : ∀ s : ℝ,
      eLpNorm (fun p => z (s, p)) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal ((c / (2 * Real.pi) + 2) * M) := by
    intro s
    by_cases hs : s ∈ Ioc 0 H
    · rw [eLpNorm_congr_ae (hz_slice s hs), eLpNorm_coe_Lp_eq]
      exact ENNReal.ofReal_le_ofReal ((B0583.norm_velocity_le c hm1 (ω s) _).trans
        (mul_le_mul_of_nonneg_left (hω_bdd s ⟨hs.1.le, hs.2⟩) hCu_pos.le))
    · have h0 : (fun p => z (s, p)) = 0 :=
        funext fun p => cPeriodicLift_eq_zero_of_notMem c H Fu hs p
      simp [h0]
  have hzq_eLp : ∀ s : ℝ,
      eLpNorm (fun p => zq (s, p)) 2 (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal M := by
    intro s
    by_cases hs : s ∈ Ioc 0 H
    · rw [eLpNorm_congr_ae (hzq_slice s hs), eLpNorm_coe_Lp_eq]
      exact ENNReal.ofReal_le_ofReal
        ((B0583.norm_velGradQ_le c hm1 (ω s)).trans (hω_bdd s ⟨hs.1.le, hs.2⟩))
    · have h0 : (fun p => zq (s, p)) = 0 :=
        funext fun p => cPeriodicLift_eq_zero_of_notMem c H Fuq hs p
      simp [h0]
  have hzη_eLp : ∀ s : ℝ,
      eLpNorm (fun p => zη (s, p)) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal (2 * M) := by
    intro s
    by_cases hs : s ∈ Ioc 0 H
    · rw [eLpNorm_congr_ae (hzη_slice s hs), eLpNorm_coe_Lp_eq]
      exact ENNReal.ofReal_le_ofReal ((B0583.norm_velGradEta_le c hm1 (ω s) _).trans
        (mul_le_mul_of_nonneg_left (hω_bdd s ⟨hs.1.le, hs.2⟩) zero_le_two))
    · have h0 : (fun p => zη (s, p)) = 0 :=
        funext fun p => cPeriodicLift_eq_zero_of_notMem c H Fuη hs p
      simp [h0]
  have hLoc_q : ∀ a b : ℝ, 0 < a →
      (∫⁻ s in Icc a b,
        (eLpNorm (fun p => z (s, p)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun p => zq (s, p)) 2 (volume.restrict (B0579.cell c)))) < ⊤ := by
    intro a b _ha
    refine (lintegral_mono fun s => ?_).trans_lt
      (lintegral_Icc_const_lt_top a b ((c / (2 * Real.pi) + 2) * M + M))
    rw [ENNReal.ofReal_add (mul_nonneg hCu_pos.le hM_nonneg) hM_nonneg]
    exact add_le_add (hz_eLp s) (hzq_eLp s)
  have hLoc_η : ∀ a b : ℝ, 0 < a →
      (∫⁻ s in Icc a b,
        (eLpNorm (fun p => z (s, p)) 2 (volume.restrict (B0579.cell c)) +
          eLpNorm (fun p => zη (s, p)) 2 (volume.restrict (B0579.cell c)))) < ⊤ := by
    intro a b _ha
    refine (lintegral_mono fun s => ?_).trans_lt
      (lintegral_Icc_const_lt_top a b ((c / (2 * Real.pi) + 2) * M + 2 * M))
    rw [ENNReal.ofReal_add (mul_nonneg hCu_pos.le hM_nonneg) (mul_nonneg zero_le_two hM_nonneg)]
    exact add_le_add (hz_eLp s) (hzη_eLp s)
  -- Step 3: Slicewise weak cylinder derivatives and `HasWeakVec` via `sliceWeakToJoint`
  have hWeak_q : ∀ s : ℝ, ∀ i : Fin 2,
      IIIa.HasWeakCellDerivC c 0 (fun p => z (s, p) i) (fun p => zq (s, p) i) := by
    intro s i
    by_cases hs : s ∈ Ioc 0 H
    · exact hasWeakCellDerivC_congr_ae
        ((hz_slice s hs).symm.mono fun p hp => congrArg (fun v : CMerid => v i) hp)
        ((hzq_slice s hs).symm.mono fun p hp => congrArg (fun v : CMerid => v i) hp)
        (hasWeakCellDerivC_of_hasWeakVelDeriv (j := i)
          (B0583.hasWeakVelDeriv_velocity_q c hm1 (ω s) (hω_circ s ⟨hs.1.le, hs.2⟩).2))
    · have hz0 : (fun p => z (s, p) i) = 0 :=
        funext fun p => by simp [z, cPeriodicLift_eq_zero_of_notMem c H Fu hs p]
      have hzq0 : (fun p => zq (s, p) i) = 0 :=
        funext fun p => by simp [zq, cPeriodicLift_eq_zero_of_notMem c H Fuq hs p]
      rw [hz0, hzq0]
      exact hasWeakCellDerivC_zero c 0
  have hWeak_η : ∀ s : ℝ, ∀ i : Fin 2,
      IIIa.HasWeakCellDerivC c 1 (fun p => z (s, p) i) (fun p => zη (s, p) i) := by
    intro s i
    by_cases hs : s ∈ Ioc 0 H
    · exact hasWeakCellDerivC_congr_ae
        ((hz_slice s hs).symm.mono fun p hp => congrArg (fun v : CMerid => v i) hp)
        ((hzη_slice s hs).symm.mono fun p hp => congrArg (fun v : CMerid => v i) hp)
        (hasWeakCellDerivC_of_hasWeakVelDeriv (j := i)
          (B0583.hasWeakVelDeriv_velocity_eta c hm1 (ω s) (hω_circ s ⟨hs.1.le, hs.2⟩).2))
    · have hz0 : (fun p => z (s, p) i) = 0 :=
        funext fun p => by simp [z, cPeriodicLift_eq_zero_of_notMem c H Fu hs p]
      have hzη0 : (fun p => zη (s, p) i) = 0 :=
        funext fun p => by simp [zη, cPeriodicLift_eq_zero_of_notMem c H Fuη hs p]
      rw [hz0, hzη0]
      exact hasWeakCellDerivC_zero c 1
  have hvQ0 : HasWeakVec vQ0 dZero z zq := by
    simpa using TailPeriodizeAux.sliceWeakToJoint hc0 0 z zq hz_sm hzq_sm hz_per hzq_per
      hLoc_q (Eventually.of_forall fun s _ i => hWeak_q s i)
  have hvEta : HasWeakVec vEta dZero z zη := by
    simpa using TailPeriodizeAux.sliceWeakToJoint hc0 1 z zη hz_sm hzη_sm hz_per hzη_per
      hLoc_η (Eventually.of_forall fun s _ i => hWeak_η s i)
  -- Slicewise weak solenoidality and periodized pairing against `IsCoordTest φ`
  have hSol_slice : ∀ (s : ℝ) (ψ : B0579.Plane → ℝ), B0579.IsCylTest c ψ →
      ∫ p in B0579.cell c,
        (z (s, p) 0 * (B0579.pd 0 ψ p : ℂ) + z (s, p) 1 * (B0579.pd 1 ψ p : ℂ)) = 0 := by
    intro s ψ hψ
    by_cases hs : s ∈ Ioc 0 H
    · have hbs := Short.IIIa.CTE.velocityIsBiotSavart c m hm_gt1 (ω s)
        (hω_circ s ⟨hs.1.le, hs.2⟩).2
      have hae : (fun p => z (s, p) 0 * (B0579.pd 0 ψ p : ℂ) +
          z (s, p) 1 * (B0579.pd 1 ψ p : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
          (fun p => (B0583.velocity c hm1 (ω s) (hω_circ s ⟨hs.1.le, hs.2⟩).2 :
              B0579.Plane → B0581.Vel) p 0 * (B0579.pd 0 ψ p : ℂ) +
            (B0583.velocity c hm1 (ω s) (hω_circ s ⟨hs.1.le, hs.2⟩).2 :
              B0579.Plane → B0581.Vel) p 1 * (B0579.pd 1 ψ p : ℂ)) :=
        (hz_slice s hs).mono fun p hp => by simp [hp]
      rw [integral_congr_ae hae]
      exact hbs.2.1 ψ hψ
    · have h0 : ∀ p, z (s, p) = 0 := cPeriodicLift_eq_zero_of_notMem c H Fu hs
      simp [h0]
  have hSol_coord : ∀ φ : Coord → ℝ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 H ×ˢ univ →
      Integrable (fun x => z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) = 0 := by
    intro φ hφ _hsupp
    obtain ⟨a, b, R, ha, hab, hR, hbox⟩ := TailPeriodizeAux.coordTest_box hφ
    have hzi_meas : ∀ i : Fin 2, AEStronglyMeasurable (fun x : Coord => z x i) volume := fun i =>
      ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_stronglyMeasurable
        hz_sm).aestronglyMeasurable
    have hzi_per : ∀ i : Fin 2, ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}),
        z (qShift c x) i = z x i :=
      fun i => hz_per.mono fun _ hx => congrArg (fun v : CMerid => v i) hx
    have hLoc_ab := hLoc_q a b ha
    have hz0_loc : (∫⁻ s in Icc a b,
        eLpNorm (fun p => z (s, p) 0) 2 (volume.restrict (B0579.cell c))) < ⊤ :=
      (lintegral_mono fun s => (eLpNorm_comp_le_merid c z s 0).trans le_self_add).trans_lt hLoc_ab
    have hz1_loc : (∫⁻ s in Icc a b,
        eLpNorm (fun p => z (s, p) 1) 2 (volume.restrict (B0579.cell c))) < ⊤ :=
      (lintegral_mono fun s => (eLpNorm_comp_le_merid c z s 1).trans le_self_add).trans_lt hLoc_ab
    have hcpd1_cont : Continuous (cpd 1 φ) :=
      (((contDiff_infty_iff_fderiv.1 hφ.smooth).2).clm_apply contDiff_const).continuous
    have hcpd2_cont : Continuous (cpd 2 φ) :=
      (((contDiff_infty_iff_fderiv.1 hφ.smooth).2).clm_apply contDiff_const).continuous
    obtain ⟨hint0, hcell0, heq0⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize hc0 ha hab hR
        (hzi_meas 0) (hzi_per 0) hz0_loc hcpd1_cont (fun x hx => (hbox x hx).2 1)
    obtain ⟨hint1, hcell1, heq1⟩ :=
      TailPeriodizeAux.integrable_and_integral_coord_eq_cell_qPeriodize hc0 ha hab hR
        (hzi_meas 1) (hzi_per 1) hz1_loc hcpd2_cont (fun x hx => (hbox x hx).2 2)
    obtain ⟨hs_int0, hz_int0⟩ := fubini_cell_slices hcell0
    obtain ⟨hs_int1, hz_int1⟩ := fubini_cell_slices hcell1
    dsimp only at hs_int0 hs_int1 hz_int0 hz_int1
    refine ⟨hint0.add hint1, ?_⟩
    rw [integral_add hint0 hint1, heq0, heq1, ← integral_add hs_int0 hs_int1]
    refine (integral_congr_ae (g := fun _ => (0 : ℂ)) ?_).trans (by simp)
    filter_upwards [hz_int0, hz_int1] with s hi0 hi1
    rw [← integral_add hi0 hi1]
    have hpd0 : (fun p => TailPeriodizeAux.qPeriodize c (cpd 1 φ) s p) =
        B0579.pd 0 (TailPeriodizeAux.qPeriodize c φ s) :=
      funext fun p => (TailPeriodizeAux.pd_qPeriodize hc0 hφ s 0 p).symm
    have hpd1 : (fun p => TailPeriodizeAux.qPeriodize c (cpd 2 φ) s p) =
        B0579.pd 1 (TailPeriodizeAux.qPeriodize c φ s) :=
      funext fun p => (TailPeriodizeAux.pd_qPeriodize hc0 hφ s 1 p).symm
    simp_rw [hpd0, hpd1]
    exact hSol_slice s (TailPeriodizeAux.qPeriodize c φ s)
      (TailPeriodizeAux.isCylTest_qPeriodize hc0 hφ s)
  refine ⟨z, zq, zη, hz_sm, hzq_sm, hzη_sm, hz_per, hzq_per, hzη_per,
    hvQ0, hvEta, hSol_coord, fun s hs => ⟨hz_slice s hs, hzq_slice s hs, hzη_slice s hs⟩⟩

end UnforcedLeray.Short.IIb.GreenVorticityUncurlNeeded

end
