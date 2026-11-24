import UnforcedLeray.Lib.TrainB.P0W1Rough

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- The horizontal difference quotient is skew-adjoint under the centered-cell L² pairing:
shifting the first argument by `h` is the same as shifting the second by `-h`. -/
theorem inner_qDifferenceQuotientCLM_eq_neg {c h : ℝ} (hc : 0 < c) (hh : h ≠ 0)
    (f ψ : L2v c) :
    inner ℝ (qDifferenceQuotientCLM hc h f) ψ =
      - inner ℝ f (qDifferenceQuotientCLM hc (-h) ψ) := by
  have hshift : inner ℝ (qShiftL2 hc h f) ψ =
      inner ℝ f (qShiftL2 hc (-h) ψ) := by
    have hmap := (qShiftL2Isometry hc (-h)).inner_map_map
      (qShiftL2 hc h f) ψ
    change inner ℝ (qShiftL2 hc (-h) (qShiftL2 hc h f))
      (qShiftL2 hc (-h) ψ) = inner ℝ (qShiftL2 hc h f) ψ at hmap
    have hinv : qShiftL2 hc (-h) (qShiftL2 hc h f) = f :=
      qShiftL2_neg_comp (a := h) hc f
    rw [hinv] at hmap
    exact hmap.symm
  change inner ℝ (h⁻¹ • (qShiftL2 hc h f - f)) ψ =
    -inner ℝ f ((-h)⁻¹ • (qShiftL2 hc (-h) ψ - ψ))
  rw [real_inner_smul_left, inner_sub_left, hshift]
  rw [real_inner_smul_right, inner_sub_right]
  have hneg : (-h)⁻¹ = -(h⁻¹) := by field_simp
  rw [hneg]
  ring

/-- A test scalar times a constant vector is a smooth, periodic, compact-axial vector field. -/
private theorem isCylSmooth_testVector {c : ℝ} {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) (v : Vec2) :
    Sob.IsCylSmooth c (fun z => φ z • v) := by
  refine ⟨hφ.smooth.smul contDiff_const, ?_, ?_⟩
  · intro z
    rw [hφ.periodic]
  · obtain ⟨R, hR⟩ := hφ.bounded
    exact ⟨R, fun z hz => by rw [hR z hz, zero_smul]⟩

/-- A strong generator for the actual centered-cell horizontal shift is the periodic weak
horizontal derivative. This is the distribution-pairing converse, with no pointwise regularity
assumed for either L² representative. -/
theorem hasWeakDeriv_qDifferenceQuotientCLM {c : ℝ} (hc : 0 < c)
    (f g : L2v c)
    (hlim : Tendsto (fun h : ℝ => qDifferenceQuotientCLM hc h f)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 g)) :
    Sob.HasWeakDeriv (Sob.cylinder c) [((1 : ℝ), (0 : ℝ))]
      (f : Plane → Vec2) (g : Plane → Vec2) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hfmem : MemLp (f : Plane → Vec2) 2 (Sob.wμ (Sob.cylinder c).μ
      (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [vecH1_measure_eq_cell c]
    exact Lp.memLp f
  have hgmem : MemLp (g : Plane → Vec2) 2 (Sob.wμ (Sob.cylinder c).μ
      (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [vecH1_measure_eq_cell c]
    exact Lp.memLp g
  refine ⟨fun φ hφ => Sob.integrable_smul_of_memLp
      (Sob.CompactlyBounded.of_adm ((Sob.cylinder c).adm_iterDirDeriv hφ
        [((1 : ℝ), (0 : ℝ))])) hfmem,
    fun φ hφ => Sob.integrable_smul_of_memLp
      (Sob.CompactlyBounded.of_adm hφ) hgmem, ?_⟩
  intro φ hφ
  have hleftInt := Sob.integrable_smul_of_memLp
    (Sob.CompactlyBounded.of_adm ((Sob.cylinder c).adm_iterDirDeriv hφ
      [((1 : ℝ), (0 : ℝ))])) hfmem
  have hrightInt := Sob.integrable_smul_of_memLp (Sob.CompactlyBounded.of_adm hφ) hgmem
  apply ext_inner_left ℝ
  intro v
  have htest := isCylSmooth_testVector hφ v
  let y : VecH1 c := Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ))
      (𝕜 := ℝ) (F := Vec2) (k := 1) (p := 2) hc
      (fun z => φ z • v) htest
  let ψ : L2v c := vecH1ValueCellCLM_MP y
  let dψ : L2v c := vecH1DqCellCLM_MP y
  have hψae : (ψ : Plane → Vec2) =ᵐ[cellμ c]
      (fun z => φ z • v) := by
    simpa [ψ, y] using vecH1ValueCellCLM_MP_ofCylSmooth_ae hc htest
  have hdψae : (dψ : Plane → Vec2) =ᵐ[cellμ c]
      (fun z => Cyl.partialQ (fun z => φ z • v) z) := by
    simpa [dψ, y] using vecH1DqCellCLM_MP_ofCylSmooth_ae hc htest
  have htestMem : MemLp (fun z => φ z • v) 2 (cellμ c) := by
    rw [← vecH1_measure_eq_cell c]
    exact htest.memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hderivEq : Cyl.partialQ (fun z => φ z • v) =
      fun z => Cyl.partialQ φ z • v := by
    funext z
    rw [Cyl.partialQ_eq_fderiv (htest.smooth.differentiable (by simp)),
      Cyl.partialQ_eq_fderiv (hφ.smooth.differentiable (by simp)),
      fderiv_smul_const (hφ.smooth.differentiable (by simp) z)]
    rfl
  have hderivMem : MemLp
      (fun z => Cyl.partialQ (fun z => φ z • v) z)
      2 (cellμ c) := by
    rw [← vecH1_measure_eq_cell c]
    have heq : (fun z => fderiv ℝ (fun z => φ z • v) z ((1 : ℝ), (0 : ℝ))) =
        (fun z => Cyl.partialQ (fun z => φ z • v) z) := by
      funext z
      exact (Cyl.partialQ_eq_fderiv
        (htest.smooth.differentiable (by simp)) z).symm
    rw [← heq]
    exact (htest.dir ((1 : ℝ), (0 : ℝ))).memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hψClass : ψ = (htestMem.toLp (fun z => φ z • v)) := by
    apply Lp.ext
    filter_upwards [hψae, htestMem.coeFn_toLp] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  have hdψClass : dψ = (hderivMem.toLp
      (fun z => Cyl.partialQ (fun z => φ z • v) z)) := by
    apply Lp.ext
    filter_upwards [hdψae, hderivMem.coeFn_toLp] with z hz₁ hz₂
    exact hz₁.trans hz₂.symm
  have htestQuotient : Tendsto (fun h : ℝ => qDifferenceQuotientCLM hc h ψ)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 dψ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [ψ, dψ, y] using
      tendsto_qDifferenceQuotientCLM_error_zero_ofCylSmooth hc htest
  have hneg : Tendsto (fun h : ℝ => -h)
      (nhdsWithin (0 : ℝ) {h : ℝ | h ≠ 0}) (nhdsWithin (0 : ℝ) {h : ℝ | h ≠ 0}) := by
    apply tendsto_nhdsWithin_iff.mpr
    have hneg0 : Tendsto (fun h : ℝ => -h) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [neg_zero] using
        (continuous_neg : Continuous (fun h : ℝ => -h)).tendsto (0 : ℝ)
    refine ⟨hneg0.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh
  have htestQuotientNeg := htestQuotient.comp hneg
  have hleftRaw : Tendsto (fun h : ℝ => inner ℝ ψ (qDifferenceQuotientCLM hc h f))
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 (inner ℝ ψ g)) :=
    ((innerSL ℝ ψ).continuous.tendsto g).comp hlim
  have hleft : Tendsto (fun h : ℝ => inner ℝ (qDifferenceQuotientCLM hc h f) ψ)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 (inner ℝ g ψ)) := by
    have heq : (fun h : ℝ => inner ℝ ψ (qDifferenceQuotientCLM hc h f)) =
        fun h => inner ℝ (qDifferenceQuotientCLM hc h f) ψ := by
      funext h
      exact real_inner_comm _ _
    rw [heq, real_inner_comm] at hleftRaw
    exact hleftRaw
  have hrightRaw : Tendsto ((fun h : ℝ => inner ℝ f (qDifferenceQuotientCLM hc h ψ)) ∘
      fun h => -h) (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 (inner ℝ f dψ)) :=
    ((innerSL ℝ f).continuous.tendsto dψ).comp htestQuotientNeg
  have hrightBase : Tendsto (fun h : ℝ => inner ℝ f
      (qDifferenceQuotientCLM hc (-h) ψ))
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 (inner ℝ f dψ)) := by
    convert hrightRaw using 1 <;> rfl
  have hright : Tendsto (fun h : ℝ => -inner ℝ f
      (qDifferenceQuotientCLM hc (-h) ψ))
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 (-inner ℝ f dψ)) := hrightBase.neg
  haveI : NeBot (nhdsWithin 0 {h : ℝ | h ≠ 0}) := by
    apply nhdsWithin_neBot.mpr
    intro s hs
    rcases Metric.mem_nhds_iff.mp hs with ⟨ε, hε, hball⟩
    refine ⟨ε / 2, hball ?_, ne_of_gt (half_pos hε)⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hpair : inner ℝ g ψ = -inner ℝ f dψ := by
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (inner_qDifferenceQuotientCLM_eq_neg hc hh f ψ).symm
  have hderivPoint : Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ))] φ = Cyl.partialQ φ := by
    funext z
    rw [Sob.iterDirDeriv_singleton, Cyl.partialQ_eq_fderiv
      (hφ.smooth.differentiable (by simp))]
  let F : Plane → Vec2 := fun z => (f : Plane → Vec2) z
  let G : Plane → Vec2 := fun z => (g : Plane → Vec2) z
  have transferIntegrable (K : Plane → Vec2) :
      Integrable K (Sob.cylinder c).μ = Integrable K (cellμ c) :=
    congrArg (fun μ : Measure Plane => Integrable K μ) (Cyl.cylinder_μ_eq c)
  have hrightCell : Integrable (fun z => φ z • (g : Plane → Vec2) z) (cellμ c) := by
    have hD : Integrable (fun z => φ z • G z) (Sob.cylinder c).μ := by
      simpa [G] using hrightInt
    exact (transferIntegrable (fun z => φ z • G z)).mp hD
  have hleftCell : Integrable
      (fun z => Cyl.partialQ φ z • (f : Plane → Vec2) z) (cellμ c) := by
    have hD : Integrable (fun z => Cyl.partialQ φ z • F z) (Sob.cylinder c).μ := by
      simpa [F, hderivPoint] using hleftInt
    exact (transferIntegrable (fun z => Cyl.partialQ φ z • F z)).mp hD
  have hpairInt : inner ℝ v (∫ z, φ z • (g : Plane → Vec2) z ∂(cellμ c)) =
      -inner ℝ v (∫ z, Cyl.partialQ φ z • (f : Plane → Vec2) z ∂(cellμ c)) := by
    have htestInner := Cyl.inner_toLp_left htestMem g
    have hderivInner := Cyl.inner_toLp_left hderivMem f
    have hpair' := hpair
    rw [hψClass, hdψClass, real_inner_comm, htestInner, real_inner_comm, hderivInner] at hpair'
    calc
      inner ℝ v (∫ z, φ z • (g : Plane → Vec2) z ∂(cellμ c)) =
          ∫ z, inner ℝ (φ z • (g : Plane → Vec2) z) v ∂(cellμ c) := by
            calc
              _ = ∫ z, inner ℝ v (φ z • (g : Plane → Vec2) z) ∂(cellμ c) :=
                (integral_inner hrightCell v).symm
              _ = _ := by
                refine integral_congr_ae ?_
                filter_upwards with z
                exact real_inner_comm _ _
      _ = ∫ z in cell c, inner ℝ (φ z • v) ((g : Plane → Vec2) z) := by
            refine integral_congr_ae ?_
            filter_upwards with z
            simp only [real_inner_smul_left]
            rw [real_inner_comm]
      _ = -∫ z in cell c,
          inner ℝ (Cyl.partialQ φ z • v) ((f : Plane → Vec2) z) := by
            rw [hderivEq] at hpair'
            exact hpair'
      _ = -inner ℝ v (∫ z, Cyl.partialQ φ z • (f : Plane → Vec2) z ∂(cellμ c)) := by
            refine congrArg Neg.neg ?_
            calc
              ∫ z in cell c, inner ℝ (Cyl.partialQ φ z • v) ((f : Plane → Vec2) z) =
                  ∫ z, inner ℝ v (Cyl.partialQ φ z • (f : Plane → Vec2) z) ∂(cellμ c) := by
                    refine integral_congr_ae ?_
                    filter_upwards with z
                    simp only [real_inner_smul_left, real_inner_smul_right]
              _ = inner ℝ v (∫ z, Cyl.partialQ φ z • (f : Plane → Vec2) z ∂(cellμ c)) :=
                    integral_inner hleftCell v
  rw [Cyl.cylinder_μ_eq, hderivPoint]
  simp only [List.length_singleton]
  norm_num
  linarith [hpairInt]

#print axioms UnforcedLeray.TrainB.inner_qDifferenceQuotientCLM_eq_neg
#print axioms UnforcedLeray.TrainB.hasWeakDeriv_qDifferenceQuotientCLM

end UnforcedLeray.TrainB
