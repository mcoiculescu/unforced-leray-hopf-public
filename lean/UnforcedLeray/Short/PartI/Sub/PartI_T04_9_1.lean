import UnforcedLeray.Short.PartI.Sub.PartI_T04_9
import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_euc
import UnforcedLeray.Short.PartI.Sub.PartI_T04_5
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.Static
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# Part I, `PartI:T04/9/1`: `APLevel2Integrated`, reduced to three leaves

Source of record: `the November 2 reference manuscript`, lines 285-288.

* `APLevel2CutCont`: time continuity of the cutoff jets on `[0,T]` (`R ≥ 1`);
* `APLevel2CutIneq`: the cutoff differential inequality, integrated in time (the PDE core);
* `APLevel2Integ`: integrability on `[0,T]` of `vortJet 2` and `triJet1` (the qualitative part).

The cutoff enstrophies use the Euclidean jets of `PartI_T04_9_1_euc` (`|Dω|² = Σ_i (∂_iω)²`,
`|D²ω|² = Σ_{ij}(∂_i∂_jω)²`, lines 285-288), which are smooth in time (the sup-norm squares are not).
`apLevel2IntegratedW_of` carries out the limit `R → ∞` (dominated convergence in the cell and in
the time integral) and compares with the operator-norm jets with the explicit constants of
`PartI_T04_9_1_euc`; its conclusion `APLevel2IntegratedW` is the integrated inequality for the
operator-norm jets `vortJet`, `triJet1` with the constants `2, 4` (the form with constants `1, 1`,
`APLevel2Integrated`, does not follow from the Euclidean inequality).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Cutoff vorticity jet `∫_cell χ_R(η) |D^j ω(s)|²` (`ω = curl v`), `|D^jω|²` the Euclidean square
for `j = 1, 2` (lines 285-288). -/
def apCutG (c : ℝ) (j : ℕ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, etaCutoff R z.2 * eucJetN j (Cyl.curl (v s)) z

/-- Cutoff trilinear majorant `4 ∫_cell χ_R(η) |Dω|² |Dv|` (`|Dω|²` Euclidean, `‖Dv‖` operator norm;
cutoff version of `triJet1`). -/
def apCutTri (c : ℝ) (v : ℝ → Plane → Vec) (R s : ℝ) : ℝ :=
  4 * ∫ z in Cyl.cell c, etaCutoff R z.2 *
    (eucJet1 (Cyl.curl (v s)) z * ‖iteratedFDeriv ℝ 1 (v s) z‖)

/-- Euclidean vorticity jet `∫_cell |D^j ω(s)|²` (`R → ∞` limit of `apCutG`). -/
def eVortJet (c : ℝ) (j : ℕ) (v : ℝ → Plane → Vec) (s : ℝ) : ℝ :=
  ∫ z in Cyl.cell c, eucJetN j (Cyl.curl (v s)) z

/-- Euclidean trilinear majorant `4 ∫_cell |Dω|² |Dv|` (`R → ∞` limit of `apCutTri`). -/
def eTriJet1 (c : ℝ) (v : ℝ → Plane → Vec) (r : ℝ) : ℝ :=
  4 * ∫ z in Cyl.cell c, eucJet1 (Cyl.curl (v r)) z * ‖iteratedFDeriv ℝ 1 (v r) z‖

/-- **Leaf (time continuity of cutoff jets)**: for `R ≥ 1` the functions `s ↦ apCutG c 2 v R s` and
`s ↦ apCutTri c v R s` are continuous on `[0,T]`.  Route: `χ_R` is smooth with support in
`|η| ≤ 2R`, so these are integrals over the compact set `[0,c] × [-2R,2R]` of functions jointly
continuous in `(s,z)` (`IsClassicalOn.smooth_v`: `v` is `C^∞` on `[0,T] × Plane`, so the iterated
derivatives are jointly continuous there); continuity of a parameter integral over a compact set
(`continuous_parametric_integral_of_continuous`, or `intervalIntegral`/dominated convergence). -/
def APLevel2CutCont : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∀ R : ℝ, 1 ≤ R →
      ContinuousOn (fun s => apCutG c 2 v R s) (Icc (0 : ℝ) T) ∧
      ContinuousOn (fun s => apCutTri c v R s) (Icc (0 : ℝ) T)

/-- **Leaf (cutoff differential inequality, integrated in time)** (lines 285-288).  For a classical
solution of the a priori class there is `C ≥ 0` with, for all `R ≥ 1`, `s ∈ [0,T]`,
`G¹_R(s) + 2ν ∫_0^s G²_R ≤ G¹_R(0) + 2 ∫_0^s Tri_R + C R^{-1/2}`.
Route: `G¹_R' = -2ν Σ_{ij} ∫χ_R (∂_i∂_jω)² - 2 ∫χ_R ∂_iω ∂_iv_j ∂_jω + E_R` on `(0,T)`
(`localVorticityEquation` for the class solution; transport term `-½∫∂_ηχ_R v_η |Dω|²`, viscous
cross term `-2ν∫ ∂_ηχ_R ∂_ηω ∂_s...`, strip errors `O(R^{-1})` times `‖·‖₂‖·‖₂` by `jet_l2` and
`HasBoundedDerivsOn`, `|χ_R'| ≤ C₀ R^{-1} √χ_R`), `apCutG c 2` is exactly `Σ_{ij}∫χ_R(∂_i∂_jω)²` (Euclidean `eucJet2`) and
`|Σ ∂_iω ∂_iv_j ∂_jω| ≤ 2 |Dω|² ‖Dv‖` (Euclidean `|Dω|²`; factor `4` in `apCutTri` is generous);
`∫_0^s E_R ≤ C R^{-1/2}`; integrate (`G_R` is `C¹` on `(0,T)` and continuous on `[0,T]`).
Adapt `Tasks/TrainGlobalExistence/APEnstrophy/{HasDeriv,Continuous,RhsEstimate}.lean` (derivative
of the cutoff enstrophy for the general class) and the `TrainSol` jet machinery under
`Tasks/DifferentiatedEnergy/ErrJetL2/VelocityJetL2/EnergyIneq/`. -/
def APLevel2CutIneq : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ s ∈ Icc (0 : ℝ) T,
      apCutG c 1 v R s + 2 * ν * ∫ r in (0 : ℝ)..s, apCutG c 2 v R r ≤
        apCutG c 1 v R 0 + 2 * (∫ r in (0 : ℝ)..s, apCutTri c v R r) + C / Real.sqrt R

/-- **Leaf (qualitative integrability)**: for a class solution `r ↦ vortJet c 2 v r` and
`r ↦ triJet1 c v r` are integrable on `[0,T]`.  Route: both are bounded on `[0,T]`
(`jet_l2`, `HasBoundedDerivsOn`, `apL2s_curl_integrableOn`, `‖D^jω‖ ≤ λ‖D^{j+1}v‖`) and are
pointwise limits (`tendsto_cutoff_integral`) of the continuous functions of `APLevel2CutCont`
(`R = n`), hence measurable. -/
def APLevel2Integ : Prop :=
  ∀ (ν c T : ℝ) (v : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), 0 < ν → 1 ≤ c →
    IsAPrioriClass ν c T v p →
      IntegrableOn (fun r => vortJet c 2 v r) (Icc (0 : ℝ) T) ∧
      IntegrableOn (fun r => triJet1 c v r) (Icc (0 : ℝ) T)

/-- Dominated convergence in the time integral. -/
theorem apL2i_tendsto_time (F : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (T s : ℝ) (hs : s ∈ Icc (0 : ℝ) T)
    (hcont : ∀ R : ℝ, 1 ≤ R → ContinuousOn (F R) (Icc (0 : ℝ) T))
    (hbound : ∀ R : ℝ, 1 ≤ R → ∀ r ∈ Icc (0 : ℝ) T, ‖F R r‖ ≤ f r)
    (hf : IntegrableOn f (Icc (0 : ℝ) T))
    (hlim : ∀ r ∈ Icc (0 : ℝ) T, Tendsto (fun R => F R r) atTop (nhds (f r))) :
    Tendsto (fun R => ∫ r in (0 : ℝ)..s, F R r) atTop (nhds (∫ r in (0 : ℝ)..s, f r)) := by
  have hsub : Ι (0 : ℝ) s ⊆ Icc (0 : ℝ) T := by
    rw [Set.uIoc_of_le hs.1]
    exact fun r hr => ⟨hr.1.le, hr.2.trans hs.2⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence f ?_ ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact ((hcont R hR).mono hsub).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact Filter.Eventually.of_forall fun r hr => hbound R hR r (hsub hr)
  · exact (intervalIntegrable_iff.2 ((hf.mono_set hsub)))
  · exact Filter.Eventually.of_forall fun r hr => hlim r (hsub hr)


/-- A pointwise limit (along `R → ∞`) of functions continuous on `[0,T]` is a.e. strongly
measurable on `[0,T]`. -/
theorem apL2i_meas_of_lim (F : ℝ → ℝ → ℝ) (f : ℝ → ℝ) (T : ℝ)
    (hF : ∀ R : ℝ, 1 ≤ R → ContinuousOn (F R) (Icc (0 : ℝ) T))
    (hlim : ∀ r ∈ Icc (0 : ℝ) T, Tendsto (fun R => F R r) atTop (nhds (f r))) :
    AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) T)) := by
  refine aestronglyMeasurable_of_tendsto_ae (μ := volume.restrict (Icc (0 : ℝ) T))
    (f := fun n : ℕ => F ((n : ℝ) + 1)) atTop ?_ ?_
  · intro n
    exact (hF _ (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)).aestronglyMeasurable
      measurableSet_Icc
  · refine ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => ?_)
    exact (hlim r hr).comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

theorem eucJetN_one (f : Plane → ℝ) (z : Plane) : eucJetN 1 f z = eucJet1 f z := by
  simp [eucJetN]

theorem eucJetN_two (f : Plane → ℝ) (z : Plane) : eucJetN 2 f z = eucJet2 f z := by
  simp [eucJetN]

/-- `PartI:T04/9/1` (limit `R → ∞`), conditional on the three leaves. -/
theorem apLevel2IntegratedW_of (hM : APLevel2CutCont) (hC : APLevel2CutIneq)
    (hI : APLevel2Integ) : APLevel2IntegratedW := by
  intro ν c T v p hν hc hcls
  obtain ⟨hI2, hIt⟩ := hI ν c T v p hν hc hcls
  refine ⟨hI2, hIt, fun s hs => ?_⟩
  obtain ⟨C, hC0, hCR⟩ := hC ν c T v p hν hc hcls
  obtain ⟨C₀, -, hF⟩ := etaCutoffFacts
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hcls.pos.le⟩
  have hu : ∀ r ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (v r) := fun r hr => by
    have h := hcls.classical.smooth_v.comp_contDiff
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : Plane => r)).prodMk contDiff_id :
        ContDiff ℝ ∞ (fun z : Plane => ((r, z) : ℝ × Plane)))
      (fun z => (⟨hr, mem_univ z⟩ : ((r, z) : ℝ × Plane) ∈ Icc (0 : ℝ) T ×ˢ univ))
    exact h
  have hcurlS : ∀ r ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (Cyl.curl (v r)) := fun r hr =>
    APEllipticCaux.curl_contDiff (hu r hr)
  have hL : ∀ r ∈ Icc (0 : ℝ) T, ∀ i : ℕ,
      IntegrableOn (fun z => ‖iteratedFDeriv ℝ i (v r) z‖ ^ 2) (Cyl.cell c) := fun r hr i => by
    obtain ⟨K, hK⟩ := hcls.jet_l2 i
    exact (hK r hr).1
  have hcurlL : ∀ r ∈ Icc (0 : ℝ) T, ∀ j : ℕ,
      IntegrableOn (fun z => ‖iteratedFDeriv ℝ j (Cyl.curl (v r)) z‖ ^ 2) (Cyl.cell c) :=
    fun r hr j => apL2s_curl_integrableOn (hu r hr) (hL r hr) j
  obtain ⟨M1, hM1⟩ := hcls.bounded 1
  have hnormv : ∀ r ∈ Icc (0 : ℝ) T, Continuous (fun z => ‖iteratedFDeriv ℝ 1 (v r) z‖) :=
    fun r hr => ((hu r hr).continuous_iteratedFDeriv (m := 1) (by exact_mod_cast le_top)).norm
  -- integrability of the jets
  have hEint : ∀ r ∈ Icc (0 : ℝ) T, ∀ j : ℕ,
      IntegrableOn (eucJetN j (Cyl.curl (v r))) (Cyl.cell c) := fun r hr j => by
    refine Integrable.mono' ((hcurlL r hr j).const_mul 4)
      (eucJetN_continuous (hcurlS r hr) j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (eucJetN_nonneg _ _ _)]
    exact eucJetN_le_norm_sq (hcurlS r hr) j z
  have hTriInt : ∀ r ∈ Icc (0 : ℝ) T, IntegrableOn (fun z =>
      ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v r) z‖) (Cyl.cell c) :=
    fun r hr => by
      refine Integrable.mono' ((hcurlL r hr 1).const_mul M1) ?_
        (Filter.Eventually.of_forall fun z => ?_)
      · exact ((((hcurlS r hr).continuous_iteratedFDeriv (m := 1)
          (by exact_mod_cast le_top)).norm.pow 2).mul (hnormv r hr)).aestronglyMeasurable
      · have hn : 0 ≤ ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 := sq_nonneg _
        rw [Real.norm_of_nonneg (mul_nonneg hn (norm_nonneg _))]
        calc ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v r) z‖
            ≤ ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * M1 :=
              mul_le_mul_of_nonneg_left (hM1 r hr z) hn
          _ = M1 * ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 := mul_comm _ _
  have hETriPt : ∀ r ∈ Icc (0 : ℝ) T, ∀ z : Plane,
      eucJet1 (Cyl.curl (v r)) z * ‖iteratedFDeriv ℝ 1 (v r) z‖ ≤
        ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v r) z‖ :=
    fun r hr z => mul_le_mul_of_nonneg_right (eucJet1_le_norm_sq (hcurlS r hr) z) (norm_nonneg _)
  have hETriI : ∀ r ∈ Icc (0 : ℝ) T, IntegrableOn (fun z =>
      eucJet1 (Cyl.curl (v r)) z * ‖iteratedFDeriv ℝ 1 (v r) z‖) (Cyl.cell c) := fun r hr => by
    refine Integrable.mono' (hTriInt r hr)
      (((eucJet1_continuous (hcurlS r hr)).mul (hnormv r hr)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (eucJet1_nonneg _ _) (norm_nonneg _))]
    exact hETriPt r hr z
  have hχ01 : ∀ R : ℝ, 1 ≤ R → ∀ z : Plane, 0 ≤ etaCutoff R z.2 ∧ etaCutoff R z.2 ≤ 1 :=
    fun R hR z => (hF R hR).2.1 z.2
  have hcmp : ∀ (g : Plane → ℝ), (∀ z, 0 ≤ g z) → IntegrableOn g (Cyl.cell c) →
      ∀ R : ℝ, 1 ≤ R →
        0 ≤ ∫ z in Cyl.cell c, etaCutoff R z.2 * g z ∧
        ∫ z in Cyl.cell c, etaCutoff R z.2 * g z ≤ ∫ z in Cyl.cell c, g z := by
    intro g hg0 hg R hR
    refine ⟨integral_nonneg fun z => mul_nonneg (hχ01 R hR z).1 (hg0 z), ?_⟩
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z =>
      mul_nonneg (hχ01 R hR z).1 (hg0 z)) hg (Filter.Eventually.of_forall fun z => ?_)
    exact mul_le_of_le_one_left (hg0 z) (hχ01 R hR z).2
  -- limits of the cutoff jets
  have hG1 : ∀ r ∈ Icc (0 : ℝ) T,
      Tendsto (fun R => apCutG c 1 v R r) atTop (nhds (eVortJet c 1 v r)) := fun r hr =>
    tendsto_cutoff_integral etaCutoffFacts c _ (hEint r hr 1)
  have hG2 : ∀ r ∈ Icc (0 : ℝ) T,
      Tendsto (fun R => apCutG c 2 v R r) atTop (nhds (eVortJet c 2 v r)) := fun r hr =>
    tendsto_cutoff_integral etaCutoffFacts c _ (hEint r hr 2)
  have hTr : ∀ r ∈ Icc (0 : ℝ) T,
      Tendsto (fun R => apCutTri c v R r) atTop (nhds (eTriJet1 c v r)) := fun r hr =>
    (tendsto_cutoff_integral etaCutoffFacts c _ (hETriI r hr)).const_mul 4
  -- comparison of the Euclidean and operator-norm jets
  have hE2le : ∀ r ∈ Icc (0 : ℝ) T, eVortJet c 2 v r ≤ 4 * vortJet c 2 v r := fun r hr => by
    unfold eVortJet vortJet
    rw [← integral_const_mul]
    exact integral_mono (hEint r hr 2) ((hcurlL r hr 2).const_mul 4)
      (fun z => eucJetN_le_norm_sq (hcurlS r hr) 2 z)
  have hE2nn : ∀ r, 0 ≤ eVortJet c 2 v r := fun r =>
    integral_nonneg fun z => eucJetN_nonneg _ _ _
  have hV2le : ∀ r ∈ Icc (0 : ℝ) T, vortJet c 2 v r ≤ 4 * eVortJet c 2 v r := fun r hr => by
    unfold eVortJet vortJet
    rw [← integral_const_mul]
    exact integral_mono (hcurlL r hr 2) ((hEint r hr 2).const_mul 4)
      (fun z => by
        rw [eucJetN_two]
        exact norm_sq_le_four_eucJet2 (hcurlS r hr) z)
  have hETle : ∀ r ∈ Icc (0 : ℝ) T, eTriJet1 c v r ≤ triJet1 c v r := fun r hr => by
    unfold eTriJet1 triJet1
    have := integral_mono (hETriI r hr) (hTriInt r hr) (hETriPt r hr)
    linarith
  have hETnn : ∀ r, 0 ≤ eTriJet1 c v r := fun r => by
    unfold eTriJet1
    exact mul_nonneg (by norm_num) (integral_nonneg fun z =>
      mul_nonneg (eucJet1_nonneg _ _) (norm_nonneg _))
  -- measurability and integrability of the Euclidean limits
  have hmE2 : AEStronglyMeasurable (fun r => eVortJet c 2 v r) (volume.restrict (Icc (0 : ℝ) T)) :=
    apL2i_meas_of_lim (fun R r => apCutG c 2 v R r) _ T
      (fun R hR => (hM ν c T v p hν hc hcls R hR).1) hG2
  have hmET : AEStronglyMeasurable (fun r => eTriJet1 c v r) (volume.restrict (Icc (0 : ℝ) T)) :=
    apL2i_meas_of_lim (fun R r => apCutTri c v R r) _ T
      (fun R hR => (hM ν c T v p hν hc hcls R hR).2) hTr
  have hE2I : IntegrableOn (fun r => eVortJet c 2 v r) (Icc (0 : ℝ) T) := by
    refine Integrable.mono' (hI2.const_mul 4) hmE2
      (ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => ?_))
    rw [Real.norm_of_nonneg (hE2nn r)]
    exact hE2le r hr
  have hETI : IntegrableOn (fun r => eTriJet1 c v r) (Icc (0 : ℝ) T) := by
    refine Integrable.mono' hIt hmET
      (ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => ?_))
    rw [Real.norm_of_nonneg (hETnn r)]
    exact hETle r hr
  -- time integrals
  have hTD := apL2i_tendsto_time (fun R r => apCutG c 2 v R r) (fun r => eVortJet c 2 v r) T s hs
    (fun R hR => (hM ν c T v p hν hc hcls R hR).1)
    (fun R hR r hr => by
      have := hcmp _ (fun z => eucJetN_nonneg _ _ _) (hEint r hr 2) R hR
      have h4 : 0 ≤ apCutG c 2 v R r := this.1
      rw [Real.norm_of_nonneg h4]
      exact this.2) hE2I hG2
  have hTT := apL2i_tendsto_time (fun R r => apCutTri c v R r) (fun r => eTriJet1 c v r) T s hs
    (fun R hR => (hM ν c T v p hν hc hcls R hR).2)
    (fun R hR r hr => by
      have := hcmp _ (fun z => mul_nonneg (eucJet1_nonneg _ _) (norm_nonneg _)) (hETriI r hr) R hR
      have h4 : 0 ≤ apCutTri c v R r := by unfold apCutTri; linarith [this.1]
      rw [Real.norm_of_nonneg h4]
      unfold apCutTri eTriJet1
      linarith [this.2]) hETI hTr
  have hsq : Tendsto (fun R : ℝ => C / Real.sqrt R) atTop (nhds 0) :=
    (tendsto_const_nhds (x := C)).div_atTop (Real.tendsto_sqrt_atTop)
  have hL1 := (hG1 s hs).add (hTD.const_mul (2 * ν))
  have hR1 := ((hG1 0 h0).add (hTT.const_mul 2)).add hsq
  rw [add_zero] at hR1
  have hEu : eVortJet c 1 v s + 2 * ν * ∫ r in (0 : ℝ)..s, eVortJet c 2 v r ≤
      eVortJet c 1 v 0 + 2 * ∫ r in (0 : ℝ)..s, eTriJet1 c v r := by
    refine le_of_tendsto_of_tendsto hL1 hR1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact hCR R hR s hs
  -- back to the operator-norm jets
  have hV1s : vortJet c 1 v s ≤ 2 * eVortJet c 1 v s := by
    unfold eVortJet vortJet
    rw [← integral_const_mul]
    refine integral_mono (hcurlL s hs 1) ((hEint s hs 1).const_mul 2) (fun z => ?_)
    rw [eucJetN_one]
    exact norm_sq_le_two_eucJet1 (hcurlS s hs) z
  have hE10 : eVortJet c 1 v 0 ≤ vortJet c 1 v 0 := by
    unfold eVortJet vortJet
    refine integral_mono (hEint 0 h0 1) (hcurlL 0 h0 1) (fun z => ?_)
    rw [eucJetN_one]
    exact eucJet1_le_norm_sq (hcurlS 0 h0) z
  have hsub : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right hs.2
  have hiV2 := intervalIntegrable_of_integrableOn_Icc hI2 hs
  have hiE2 := intervalIntegrable_of_integrableOn_Icc hE2I hs
  have hiT := intervalIntegrable_of_integrableOn_Icc hIt hs
  have hiET := intervalIntegrable_of_integrableOn_Icc hETI hs
  have hint2 : ∫ r in (0 : ℝ)..s, vortJet c 2 v r ≤ 4 * ∫ r in (0 : ℝ)..s, eVortJet c 2 v r := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hs.1 hiV2 (hiE2.const_mul 4)
      (fun r hr => hV2le r ⟨hr.1, hr.2.trans hs.2⟩)
  have hintT : ∫ r in (0 : ℝ)..s, eTriJet1 c v r ≤ ∫ r in (0 : ℝ)..s, triJet1 c v r :=
    intervalIntegral.integral_mono_on hs.1 hiET hiT
      (fun r hr => hETle r ⟨hr.1, hr.2.trans hs.2⟩)
  nlinarith [hEu, hV1s, hE10, hint2, hintT]

end UnforcedLeray.Short.PartI
