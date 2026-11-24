import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Tasks.OverlapRescaling

/-!
# `PartI:T21` (`Sub/PartI_T21.lean`): transverse tails and weighted bounds for `(ψ, v, p)`

Source of record: `the November 2 reference manuscript`, lines 499-526
(old 493-515), in the proof of Lemma `sct:heat`.

This module defines the two leaf obligations for `PartI:T21`:
* `TrainStreamVelocityPressureTransverseTail` (`PartI:T21/1`, source lines 499-518)
* `TrainWeightedJetBounds` (`PartI:T21/2`, source lines 518-526)

and proves:
1. **Evenness of the decaying stream and mean stream** (`PartI_T21.train_stream_even`,
   `PartI_T21.train_meanStream_even`, `PartI_T21.train_meanStream_even_all`):
   `tr.ψ s (-z) = tr.ψ s z` and `meanStream tr s (-η) = meanStream tr s η` for all `s ≥ 0`
   (Conjunct 1 of `TrainStreamVelocityPressureTails`, proved unconditionally).
2. **Reduction of `wCellL2 c m` to `wSupNorm (m + 2)`** (`PartI_T21.wCellL2_le_of_wSupNorm_add_two`
   and `PartI_T21.trainWeightedJetBounds_of_wSupNorm`):
   since `(1 + z.2²)⁻¹ ∈ L²(Cyl.cell 1)` and `jap (m + 2) z = jap m z * (1 + z.2²)²`,
   any `wSupNorm (m + 2)` bound on `f` automatically implies the `wCellL2 c m` bound on `f`
   with at most an extra factor of `c`.
3. **Conditional assembly of `TrainStreamVelocityPressureTails`**
   (`train_stream_velocity_pressure_tails_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec jet cellL2 wCellL2 jap)

/-! ### 1. Leaf obligations for Conjuncts 2 and 3 (`PartI:T21/1` and `PartI:T21/2`) -/

/-- **Leaf 1 (`PartI:T21/1`): transverse tails for `(ψ, v, p)`** (source lines 499-518):
for every `ρ > 1/2` and `(ℓ, j)`, there exist `b, C₀, C', C > 0`, `N : ℕ`, and `ν₀ > 0`
(uniform in `S_* ≥ 0`) such that for `0 < s ≤ S_*` and `|z.2| ≥ C'/ν + 2 + l` (`l ≥ 0`),
the mixed age/spatial jets `ageJet ℓ j` of `(tr.ψ, tr.v, tr.p)` are bounded by
`polyPS C N ν c S_* * (exp(-b l / c) + exp(-b l² / (C₀ + ν S_*)))`. -/
def TrainStreamVelocityPressureTransverseTail : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ℓ j : ℕ, ∃ b C₀ C' : ℝ, 0 < b ∧ 0 < C₀ ∧ 0 < C' ∧
    ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧ ∀ S_ : ℝ, 0 ≤ S_ →
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ l : ℝ, 0 ≤ l → ∀ s : ℝ, 0 < s → s ≤ S_ → ∀ z : Plane, C' / ν + 2 + l ≤ |z.2| →
          let c := trainPeriod ρ ν
          let K : ℝ := polyPS C N ν c S_ *
            (Real.exp (-(b * l / c)) + Real.exp (-(b * l ^ 2 / (C₀ + ν * S_))))
          ‖ageJet ℓ j tr.ψ s z‖ ≤ K ∧ ‖ageJet ℓ j tr.v s z‖ ≤ K ∧ ‖ageJet ℓ j tr.p s z‖ ≤ K

/-- **Leaf 2 (`PartI:T21/2`): polynomial weighted `L²` and `L^∞` bounds for `(ψ̃, ṽ, v, ω, p)`**
(source lines 518-526):
for every `ρ > 1/2` and `(m, ℓ, j)`, there exist `C > 0`, `N : ℕ`, and `ν₀ > 0` such that at
every age `s > 0`, both `wCellL2 c m` and `wSupNorm m` of `ageJet ℓ j` of `(ψ̃, ṽ, v, ω, p)`
are bounded by `ENNReal.ofReal (polyPS C N ν c s)`. -/
def TrainWeightedJetBounds : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∀ m ℓ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
        let c := trainPeriod ρ ν
        let K : ℝ≥0∞ := ENNReal.ofReal (polyPS C N ν c s)
        (wCellL2 c m (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K ∧
          wSupNorm m (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K) ∧
        (wCellL2 c m (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K ∧
          wSupNorm m (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K) ∧
        (wCellL2 c m (ageJet ℓ j tr.v s) ≤ K ∧ wSupNorm m (ageJet ℓ j tr.v s) ≤ K) ∧
        (wCellL2 c m (ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s) ≤ K ∧
          wSupNorm m (ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s) ≤ K) ∧
        (wCellL2 c m (ageJet ℓ j tr.p s) ≤ K ∧ wSupNorm m (ageJet ℓ j tr.p s) ≤ K)

namespace PartI_T21

/-! ### 2. Unconditional proof of stream evenness and Conjunct 1 (`train_meanStream_even`) -/

/-- **Evenness of the decaying stream `ψ` (`ψ(s, -z) = ψ(s, z)`)**:
for any train `tr : B0140.TrainSol ν c` and any age `s ≥ 0`, central oddness `v(s, -z) = -v(s, z)`
together with `v = ∇^⊥ ψ` and `ψ(s, z) → 0` as `|z.2| → ∞` implies `tr.ψ s (-z) = tr.ψ s z`
for all `z : Plane`. -/
theorem train_stream_even {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (z : Plane) :
    tr.ψ s (-z) = tr.ψ s z := by
  have hψd : Differentiable ℝ (tr.ψ s) := tr.isTrain.stream_differentiable s hs
  have hstream := tr.isTrain.stream s hs
  have hodd := tr.isTrain.odd s hs
  have hHasY : ∀ a y : ℝ, HasDerivAt (fun y' => tr.ψ s (a, y')) (-(tr.v s (a, y) 0)) y := by
    intro a y
    have hd : DifferentiableAt ℝ (fun y' => tr.ψ s (a, y')) y :=
      (hψd (a, y)).comp y ((differentiableAt_const a).prodMk differentiableAt_id)
    have he : tr.v s (a, y) 0 = -deriv (fun y' => tr.ψ s (a, y')) y := by
      rw [hstream (a, y)]
      rfl
    rw [he, neg_neg]
    exact hd.hasDerivAt
  have hEvenPt : ∀ q y : ℝ, tr.ψ s (-q, -y) = tr.ψ s (q, y) := by
    intro q y
    have hD : ∀ y' : ℝ, HasDerivAt (fun y'' => tr.ψ s (-q, -y'') - tr.ψ s (q, y'')) 0 y' := by
      intro y'
      have hnegY : HasDerivAt (fun y'' => tr.ψ s (-q, -y''))
          (-(tr.v s (-q, -y') 0) * -1) y' :=
        (hHasY (-q) (-y')).comp y' (hasDerivAt_id y').neg
      have hodd0 : tr.v s (-q, -y') 0 = -(tr.v s (q, y') 0) := by
        have h := congrArg (fun w : Vec => w 0) (hodd (q, y'))
        simpa using h
      have h := hnegY.sub (hHasY q y')
      have e : -(tr.v s (-q, -y') 0) * -1 - -(tr.v s (q, y') 0) = 0 := by
        rw [hodd0]
        ring
      rw [e] at h
      exact h
    have hconst : ∀ y' : ℝ,
        tr.ψ s (-q, -y') - tr.ψ s (q, y') = tr.ψ s (-q, 0) - tr.ψ s (q, 0) := by
      intro y'
      have h := is_const_of_deriv_eq_zero (fun t => (hD t).differentiableAt)
        (fun t => (hD t).deriv) y' 0
      simpa using h
    have hl_pos : Tendsto (fun y' : ℝ => tr.ψ s (q, y')) atTop (𝓝 0) := by
      have hmap : Tendsto (fun y' : ℝ => ((q, y') : Plane)) atTop
          (comap (fun w : Plane => |w.2|) atTop) := by
        rw [tendsto_comap_iff]
        exact tendsto_abs_atTop_atTop
      exact (tr.isTrain.stream_decay s hs).comp hmap
    have hl_neg : Tendsto (fun y' : ℝ => tr.ψ s (-q, -y')) atTop (𝓝 0) := by
      have hmap : Tendsto (fun y' : ℝ => ((-q, -y') : Plane)) atTop
          (comap (fun w : Plane => |w.2|) atTop) := by
        rw [tendsto_comap_iff]
        have habs : (fun w : Plane => |w.2|) ∘ (fun y' : ℝ => ((-q, -y') : Plane)) =
            fun y' : ℝ => |y'| := by
          funext y'
          simp [abs_neg]
        rw [habs]
        exact tendsto_abs_atTop_atTop
      exact (tr.isTrain.stream_decay s hs).comp hmap
    have hlim : Tendsto (fun y' : ℝ => tr.ψ s (-q, -y') - tr.ψ s (q, y')) atTop (𝓝 0) := by
      simpa only [sub_zero] using hl_neg.sub hl_pos
    have hzero : tr.ψ s (-q, 0) - tr.ψ s (q, 0) = 0 :=
      tendsto_nhds_unique tendsto_const_nhds (Tendsto.congr hconst hlim)
    exact sub_eq_zero.1 ((hconst y).trans hzero)
  exact hEvenPt z.1 z.2

/-- **Evenness of the mean stream `S(s, -η) = S(s, η)`** (source line 499; Conjunct 1 of
`TrainStreamVelocityPressureTails`):
for any `c > 0`, any train `tr : B0140.TrainSol ν c`, any `s ≥ 0`, and any `η : ℝ`,
`meanStream tr s (-η) = meanStream tr s η`. -/
theorem train_meanStream_even {ν c : ℝ} (hc : 0 < c) (tr : B0140.TrainSol ν c)
    (s : ℝ) (hs : 0 ≤ s) (η : ℝ) :
    meanStream tr s (-η) = meanStream tr s η := by
  unfold meanStream hmean
  congr 1
  have hle : -c / 2 ≤ c / 2 := by linarith
  rw [← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
  have heq : (fun q : ℝ => tr.ψ s (q, -η)) = (fun q : ℝ => tr.ψ s (-q, η)) := by
    funext q
    have h := train_stream_even tr hs (-q, η)
    change tr.ψ s (- -q, -η) = tr.ψ s (-q, η) at h
    rwa [neg_neg] at h
  rw [heq, intervalIntegral.integral_comp_neg (fun q : ℝ => tr.ψ s (q, η))]
  have h1 : -(c / 2) = -c / 2 := by ring
  have h2 : -(-c / 2) = c / 2 := by ring
  rw [h1, h2]

/-- Conjunct 1 of `TrainStreamVelocityPressureTails`, proved unconditionally. -/
theorem train_meanStream_even_all :
    ∀ ρ : ℝ, 1 / 2 < ρ → ∀ ν : ℝ, 0 < ν →
      ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr →
        ∀ s : ℝ, 0 ≤ s → ∀ η : ℝ, meanStream tr s (-η) = meanStream tr s η := by
  intro ρ _hρ ν hν tr _htr s hs η
  exact train_meanStream_even (Real.rpow_pos_of_pos hν (-ρ)) tr s hs η

/-! ### 3. Reduction of `wCellL2 c m` to `wSupNorm (m + 2)` -/

theorem jap_mono {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) (z : Plane) : jap m₁ z ≤ jap m₂ z := by
  unfold jap
  exact pow_le_pow_right₀ (by nlinarith [sq_nonneg z.2]) hm

theorem wSupNorm_mono {E : Type*} [NormedAddCommGroup E] {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂)
    (f : Plane → E) : wSupNorm m₁ f ≤ wSupNorm m₂ f := by
  unfold wSupNorm
  apply iSup_mono
  intro z
  gcongr
  exact jap_mono hm z

theorem sqrt_jap_add_two (m : ℕ) (z : Plane) :
    Real.sqrt (jap (m + 2) z) = Real.sqrt (jap m z) * (1 + z.2 ^ 2) := by
  have h : jap (m + 2) z = jap m z * (1 + z.2 ^ 2) ^ 2 := by
    unfold jap
    rw [pow_add]
  have hnn : 0 ≤ jap m z := by unfold jap; positivity
  rw [h, Real.sqrt_mul hnn, Real.sqrt_sq (by positivity)]

private theorem inv_one_add_sq_memLp_unit :
    MemLp (fun y : Plane => (1 + y.2 ^ 2)⁻¹) 2 (Cyl.cellμ 1) := by
  have hφ : Integrable (fun x : ℝ => ((1 + x ^ 2)⁻¹) ^ 2) := by
    refine integrable_inv_one_add_sq.mono' ?_ ?_
    · have hc : Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹) :=
        Continuous.inv₀ (by fun_prop) (fun x => by positivity)
      exact (hc.pow 2).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      have h1 : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [show 0 ≤ (1 + x ^ 2)⁻¹ by positivity]
  have hcont : Continuous (fun y : Plane => (1 + y.2 ^ 2)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun y => by positivity)
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
  rw [Cyl.cellμ_eq_prod]
  have : IsFiniteMeasure (volume.restrict (Set.Ico (-1 / 2 : ℝ) (1 / 2))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ico_lt_top⟩
  exact hφ.comp_snd _

/-- Universal constant `W₀ = ‖(1 + y.2²)⁻¹‖_{L²(Cyl.cell 1)} + 1 > 0`. -/
def unitCellInvSqL2 : ℝ :=
  (eLpNorm (fun y : Plane => (1 + y.2 ^ 2)⁻¹) 2 (Cyl.cellμ 1)).toReal + 1

theorem unitCellInvSqL2_pos : 0 < unitCellInvSqL2 := by
  unfold unitCellInvSqL2
  positivity

/-- For any `c ≥ 1`, `m : ℕ`, `f : Plane → E`, and `B ≥ 0`, if
`wSupNorm (m + 2) f ≤ ENNReal.ofReal B`, then
`wCellL2 c m f ≤ ENNReal.ofReal (unitCellInvSqL2 * c * B)`. -/
theorem wCellL2_le_of_wSupNorm_add_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c B : ℝ} (hc : 1 ≤ c) (hB : 0 ≤ B) (m : ℕ) (f : Plane → E)
    (hSup : wSupNorm (m + 2) f ≤ ENNReal.ofReal B) :
    wCellL2 c m f ≤ ENNReal.ofReal (unitCellInvSqL2 * c * B) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  let G : Plane → ℝ := fun z => (1 + z.2 ^ 2)⁻¹
  have hG_cont : Continuous G := Continuous.inv₀ (by fun_prop) (fun z => by positivity)
  have hpt : ∀ z : Plane, ‖Real.sqrt (jap m z) • f z‖ₑ ≤ ‖(B • G) z‖ₑ := by
    intro z
    have hz : ENNReal.ofReal (Real.sqrt (jap (m + 2) z)) * ‖f z‖ₑ ≤ ENNReal.ofReal B :=
      (le_iSup (fun w : Plane => ENNReal.ofReal (Real.sqrt (jap (m + 2) w)) * ‖f w‖ₑ) z).trans hSup
    have hp1 : 0 < 1 + z.2 ^ 2 := by positivity
    have hjm : 0 ≤ Real.sqrt (jap m z) := Real.sqrt_nonneg _
    have hjm2 : 0 ≤ Real.sqrt (jap (m + 2) z) := Real.sqrt_nonneg _
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hjm2] at hz
    have hz_real : Real.sqrt (jap (m + 2) z) * ‖f z‖ ≤ B :=
      (ENNReal.ofReal_le_ofReal_iff hB).1 hz
    rw [sqrt_jap_add_two] at hz_real
    have hle_real : ‖Real.sqrt (jap m z) • f z‖ ≤ B * G z := by
      rw [norm_smul, Real.norm_of_nonneg hjm]
      dsimp only [G]
      rw [← div_eq_mul_inv, le_div_iff₀ hp1]
      linarith
    have hBG_nn : 0 ≤ B * G z := mul_nonneg hB (by positivity)
    rw [Pi.smul_apply, smul_eq_mul, Real.enorm_eq_ofReal hBG_nn, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hle_real
  have hmono : wCellL2 c m f ≤ eLpNorm (B • G) 2 (Cyl.cellμ c) :=
    eLpNorm_mono_enorm hpt
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hB] at hmono
  have hscale := cellL2_one_comp_smul hc0 hG_cont
  have hG_cell : eLpNorm G 2 (Cyl.cellμ c) =
      ENNReal.ofReal c * cellL2 1 (fun y : Plane => G (c • y)) := by
    unfold cellL2 at hscale ⊢
    rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul hc0.le, mul_inv_cancel₀ hc0.ne',
      ENNReal.ofReal_one, one_mul]
  have hG_le1 : cellL2 1 (fun y : Plane => G (c • y)) ≤ ENNReal.ofReal unitCellInvSqL2 := by
    have hm : cellL2 1 (fun y : Plane => G (c • y)) ≤ cellL2 1 G := by
      apply eLpNorm_mono_real
      intro y
      rw [Real.norm_of_nonneg (by positivity)]
      apply inv_anti₀ (by positivity)
      have hc2 : 1 ≤ c ^ 2 := by nlinarith
      have : y.2 ^ 2 ≤ (c * y.2) ^ 2 := by
        rw [mul_pow]
        nlinarith [sq_nonneg y.2]
      simpa [G, Prod.smul_mk, smul_eq_mul] using add_le_add_left this 1
    have hlt := inv_one_add_sq_memLp_unit.eLpNorm_lt_top
    have heq : cellL2 1 G = ENNReal.ofReal (cellL2 1 G).toReal :=
      (ENNReal.ofReal_toReal hlt.ne).symm
    rw [heq] at hm
    refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold unitCellInvSqL2 cellL2
    linarith
  calc wCellL2 c m f
      ≤ ENNReal.ofReal B * (ENNReal.ofReal c * ENNReal.ofReal unitCellInvSqL2) := by
        refine hmono.trans ?_
        rw [hG_cell]
        gcongr
    _ = ENNReal.ofReal (unitCellInvSqL2 * c * B) := by
        rw [← ENNReal.ofReal_mul hc0.le, ← ENNReal.ofReal_mul hB]
        congr 1
        ring

/-- Single-field reduction: a `polyPS C N ν c s` bound on `wSupNorm (m + 2) f` implies both
`wCellL2 c m f` and `wSupNorm m f` are bounded by `polyPS ((1 + unitCellInvSqL2) * C) (N + 1) ν c s`. -/
theorem wCellL2_and_wSupNorm_polyPS_of_wSupNorm_add_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C ν c s : ℝ} {N m : ℕ} (hC : 0 < C) (hν : 0 < ν) (hc : 1 ≤ c) (hs : 0 < s)
    (f : Plane → E)
    (hSup : wSupNorm (m + 2) f ≤ ENNReal.ofReal (polyPS C N ν c s)) :
    let C' := (1 + unitCellInvSqL2) * C
    wCellL2 c m f ≤ ENNReal.ofReal (polyPS C' (N + 1) ν c s) ∧
      wSupNorm m f ≤ ENNReal.ofReal (polyPS C' (N + 1) ν c s) := by
  intro C'
  have hW : 0 < unitCellInvSqL2 := unitCellInvSqL2_pos
  have hB : 0 ≤ polyPS C N ν c s := by
    unfold polyPS
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    positivity
  have hbase_ge : 1 ≤ (1 + c + ν⁻¹) * (1 + s) := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    nlinarith
  have hc_le : c ≤ (1 + c + ν⁻¹) * (1 + s) := by
    have : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    nlinarith
  have hC1 : C ≤ C' := by
    change C ≤ (1 + unitCellInvSqL2) * C
    nlinarith
  have hC2 : unitCellInvSqL2 * C ≤ C' := by
    change unitCellInvSqL2 * C ≤ (1 + unitCellInvSqL2) * C
    nlinarith
  have hK1 : polyPS C N ν c s ≤ polyPS C' (N + 1) ν c s := by
    unfold polyPS
    rw [pow_succ]
    calc C * ((1 + c + ν⁻¹) * (1 + s)) ^ N
        ≤ C' * ((1 + c + ν⁻¹) * (1 + s)) ^ N * 1 := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right hC1 (by positivity)
      _ ≤ C' * ((1 + c + ν⁻¹) * (1 + s)) ^ N * ((1 + c + ν⁻¹) * (1 + s)) :=
          mul_le_mul_of_nonneg_left hbase_ge (by positivity)
      _ = C' * (((1 + c + ν⁻¹) * (1 + s)) ^ N * ((1 + c + ν⁻¹) * (1 + s))) := by ring
  have hK2 : unitCellInvSqL2 * c * polyPS C N ν c s ≤ polyPS C' (N + 1) ν c s := by
    unfold polyPS
    rw [pow_succ]
    calc unitCellInvSqL2 * c * (C * ((1 + c + ν⁻¹) * (1 + s)) ^ N)
        = (unitCellInvSqL2 * C) * ((1 + c + ν⁻¹) * (1 + s)) ^ N * c := by ring
      _ ≤ C' * ((1 + c + ν⁻¹) * (1 + s)) ^ N * ((1 + c + ν⁻¹) * (1 + s)) := by
          apply mul_le_mul _ hc_le (by linarith) (by positivity)
          exact mul_le_mul_of_nonneg_right hC2 (by positivity)
      _ = C' * (((1 + c + ν⁻¹) * (1 + s)) ^ N * ((1 + c + ν⁻¹) * (1 + s))) := by ring
  exact ⟨(wCellL2_le_of_wSupNorm_add_two hc hB m f hSup).trans (ENNReal.ofReal_le_ofReal hK2),
    ((wSupNorm_mono (Nat.le_add_right m 2) f).trans hSup).trans (ENNReal.ofReal_le_ofReal hK1)⟩

/-- **Reduction of `TrainWeightedJetBounds` (`PartI:T21/2`) to `wSupNorm` bounds alone**:
if for every `ρ > 1/2` and `(m, ℓ, j)` the 5 fields `(ψ̃, ṽ, v, ω, p)` satisfy the
`wSupNorm m` bound with `polyPS C N ν c s`, then `TrainWeightedJetBounds` holds (covering
both `wCellL2 c m` and `wSupNorm m`). -/
theorem trainWeightedJetBounds_of_wSupNorm
    (hSup : ∀ ρ : ℝ, 1 / 2 < ρ → ∀ m ℓ j : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∃ ν₀ : ℝ, 0 < C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : B0140.TrainSol ν (trainPeriod ρ ν), IsBUCTrain tr → ∀ s : ℝ, 0 < s →
          let c := trainPeriod ρ ν
          let K : ℝ≥0∞ := ENNReal.ofReal (polyPS C N ν c s)
          wSupNorm m (ageJet ℓ j (fun r z => tr.ψ r z - hmean c (tr.ψ r) z.2) s) ≤ K ∧
          wSupNorm m (ageJet ℓ j (fun r => hfluct c (tr.v r)) s) ≤ K ∧
          wSupNorm m (ageJet ℓ j tr.v s) ≤ K ∧
          wSupNorm m (ageJet ℓ j (fun r w => Cyl.curl (tr.v r) w) s) ≤ K ∧
          wSupNorm m (ageJet ℓ j tr.p s) ≤ K) :
    TrainWeightedJetBounds := by
  intro ρ hρ m ℓ j
  obtain ⟨C, N, ν₀, hC, hν₀, hS⟩ := hSup ρ hρ (m + 2) ℓ j
  have hW : 0 < unitCellInvSqL2 := unitCellInvSqL2_pos
  refine ⟨(1 + unitCellInvSqL2) * C, N + 1, min ν₀ (1 / 2), by positivity,
    lt_min hν₀ (by norm_num), ?_⟩
  intro ν hν hν_le tr htr s hs
  have hν₀_le : ν ≤ ν₀ := hν_le.trans (min_le_left _ _)
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  have hc1 : 1 ≤ trainPeriod ρ ν := by
    unfold trainPeriod
    exact (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hν (by linarith) (by linarith)).le
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS ν hν hν₀_le tr htr s hs
  exact ⟨wCellL2_and_wSupNorm_polyPS_of_wSupNorm_add_two hC hν hc1 hs _ h1,
    wCellL2_and_wSupNorm_polyPS_of_wSupNorm_add_two hC hν hc1 hs _ h2,
    wCellL2_and_wSupNorm_polyPS_of_wSupNorm_add_two hC hν hc1 hs _ h3,
    wCellL2_and_wSupNorm_polyPS_of_wSupNorm_add_two hC hν hc1 hs _ h4,
    wCellL2_and_wSupNorm_polyPS_of_wSupNorm_add_two hC hν hc1 hs _ h5⟩

end PartI_T21

/-- **Conditional assembly of `PartI:T21` (`train_stream_velocity_pressure_tails_of`)**:
combines the unconditional proof of `PartI_T21.train_meanStream_even_all` with the two leaf
obligations `TrainStreamVelocityPressureTransverseTail` and `TrainWeightedJetBounds`. -/
theorem train_stream_velocity_pressure_tails_of
    (hTail : TrainOverlap → TrainVorticityGaussianTail →
      TrainStreamVelocityPressureTransverseTail)
    (hWeight : TrainOverlap → TrainVorticityGaussianTail →
      TrainStreamVelocityPressureTransverseTail → TrainWeightedJetBounds)
    (hOv : TrainOverlap) (hVort : TrainVorticityGaussianTail) :
    TrainStreamVelocityPressureTails := by
  have hT := hTail hOv hVort
  exact ⟨PartI_T21.train_meanStream_even_all, hT, hWeight hOv hVort hT⟩

end UnforcedLeray.Short.PartI
