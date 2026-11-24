import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanCoeff
import UnforcedLeray.Short.PartIIa.Tasks.R07BoundedDerivs.JetUnif
import UnforcedLeray.Short.PartIIa.Tasks.R07BoundedDerivs.TrainWtdPoly
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftBdd_Sub
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof

/-!
# Part II-a, task `PartII-a:R07`: bounded spatial derivatives of the similarity profile (`RingBoundedDerivs`)

Source of record: `the November 2 reference manuscript`, lines 1217-1219 and
1305-1325.

Proves `theorem ringBoundedDerivs : RingBoundedDerivs` unconditionally by combining:
1. `ringAxisSmooth` (`Short/PartII-a/Tasks/R06AxisSmooth.lean`) for the smooth extension across the
   symmetry axis;
2. `nv_jet_le_unif` and `heatSum_jet_le_unif` (`Tasks/R07BoundedDerivs/JetUnif.lean`) for
   `R`-uniform lift and heat-sum jet bounds;
3. `early_stream_wtd_jet_poly` and `late_heatRem_wtd_jet_poly`
   (`Tasks/R07BoundedDerivs/TrainWtdPoly.lean`) for `(ν, c)`-polynomial weighted joint-derivative
   bounds at early (`s ≤ 1`) and late (`s ≥ 1`) ages;
4. density of `{y : Space | Axi.ϱ y ≠ 0}` (`Cons.C03.dense_compl_axis`) and continuity of
   `y ↦ ‖iteratedFDeriv ℝ j (U τ) y‖` to extend the off-axis bound across the axis.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0190
open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.PartIIIb.Concrete
  (heatSum Nv_heat_decomp contDiff_heatSum ringLiftPtJet ringProfileMeridJet varrho_ne_zero_iff)

/-- Off-axis Cartesian jet bound for a single derivative order `j : ℕ`, uniform in `R ≥ 2` and
`τ : ℝ`, with polynomial majorant `polyConst C d ν (ν ^ (-ρ))`. -/
theorem ringOffAxisDerivBdd (hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hME : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    {ρ : ℝ} (hρ : 1 / 2 < ρ) (j : ℕ) :
    ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ ψ pr : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ pr →
          ∀ R : ℝ, 2 ≤ R → ∀ (τ : ℝ) (y : Space), Axi.ϱ y ≠ 0 →
            ‖iteratedFDeriv ℝ j (simProfile 1 (liftVelocity R ψ) τ) y‖ ≤
              polyConst C d ν (ν ^ (-ρ)) := by
  obtain ⟨Cnv, K, hCnv0, Hnv⟩ := nv_jet_le_unif j
  obtain ⟨CJ, KJ, hCJ, HJ⟩ := ringLiftPtJet j
  have hP := ringProfileMeridJet
  set N : ℕ := K + j + 2 with hNdef
  -- Early-age (`s ≤ 1`) weighted joint-derivative bounds for `i ∈ range (j + 2)`
  have hexF : ∀ i : ℕ, ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 → x.1 ≤ 1 →
            (1 + |x.2.2|) ^ (j + 1) *
              ‖iteratedFDeriv ℝ i (fun z : ℝ × (ℝ × ℝ) => tr.ψ z.1 z.2) x‖ ≤
                polyConst C d ν (ν ^ (-ρ)) :=
    fun i => early_stream_wtd_jet_poly hFD hME hρ (j + 1) i
  choose νF CF dF hνF hCF hbdF using hexF
  -- Late-age (`1 ≤ s`) weighted joint-derivative bounds for `heatRemainder` and `i ∈ range (j + 2)`
  have hexN : ∀ i : ℕ, ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-ρ)),
          UnforcedLeray.Short.PartI.IsBUCTrain tr →
          ∀ x : ℝ × (ℝ × ℝ), 1 ≤ x.1 →
            (1 + |x.2.2|) ^ (j + 1) *
              ‖iteratedFDeriv ℝ i
                (heatRemainder ν (UnforcedLeray.Short.PartI.meanCoeff tr) N
                  (fun z => tr.ψ z.1 z.2)) x‖ ≤
                polyConst C d ν (ν ^ (-ρ)) * x.1 ^ (((j + 1 : ℕ) : ℝ) / 2 - N - 3 / 2) :=
    fun i => late_heatRem_wtd_jet_poly hFD hME hρ N (j + 1) i
  choose νN CN dN hνN hCN hbdN using hexN
  -- Heat-sum jet bound on `ϱ y ^ 2 ≤ R ^ 2`
  obtain ⟨νH, CH, dH, hνH, hCH, Hh⟩ :=
    heatSum_jet_le_unif (lateMeanCoeff_of hFD UnforcedLeray.Short.PartI.trainMeanEquations_proof)
      hρ N j
  set I := Finset.range (j + 2)
  have hSνF : 0 ≤ ∑ i ∈ I, 1 / νF i :=
    Finset.sum_nonneg fun i _ => (one_div_pos.2 (hνF i)).le
  have hSνN : 0 ≤ ∑ i ∈ I, 1 / νN i :=
    Finset.sum_nonneg fun i _ => (one_div_pos.2 (hνN i)).le
  set ν₀F := 1 / (1 + ∑ i ∈ I, 1 / νF i)
  set ν₀N := 1 / (1 + ∑ i ∈ I, 1 / νN i)
  set ν₀ := min νH (min ν₀F ν₀N)
  have hν₀ : 0 < ν₀ := lt_min hνH (lt_min (inv_one_add_pos hSνF) (inv_one_add_pos hSνN))
  set sumCF := ∑ i ∈ I, CF i
  set sumCN := ∑ i ∈ I, CN i
  set sumdF := ∑ i ∈ I, dF i
  set sumdN := ∑ i ∈ I, dN i
  have hsumCF0 : 0 ≤ sumCF := Finset.sum_nonneg fun i _ => hCF i
  have hsumCN0 : 0 ≤ sumCN := Finset.sum_nonneg fun i _ => hCN i
  set C_early := Cnv * 2 ^ (K + 1) * sumCF
  set C_late := CH + Cnv * 2 ^ (K + 1) * sumCN
  set C := C_early + C_late
  set d := max sumdF (max dH sumdN)
  have hC_early0 : 0 ≤ C_early := by positivity
  have hC_late0 : 0 ≤ C_late := by positivity
  refine ⟨ν₀, C, d, hν₀, add_nonneg hC_early0 hC_late0,
    fun ν hν0 hνle ψ pr hpr R hR τ y hy0 => ?_⟩
  obtain ⟨T, hT, hψ, -⟩ := hpr
  subst hψ
  have hc0 : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hνleH : ν ≤ νH := hνle.trans (min_le_left _ _)
  have hνleF : ν ≤ ν₀F := hνle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hνleN : ν ≤ ν₀N := hνle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hΨ : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) (Ioi 0 ×ˢ univ) :=
    UnforcedLeray.Short.PartI.trainStreamSmooth ν _ hν0 hc0 T hT
  have hmer : ∀ x : ℝ × (ℝ × ℝ), 0 < x.1 →
      merProfile R (trainProfile T.ψ) x =
        Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) x := by
    intro x hx
    rw [← rawProfile_eq_merProfile_of_smooth UnforcedLeray.Short.PartI.trainStreamSmooth
      hν0 hc0 T hT (R := R) rfl hx]
    exact rawStreamProfile ν _ R T hR0 hΨ x hx
  have hy : y ∉ Axi.axis := varrho_ne_zero_iff.1 hy0
  have hevU : simProfile 1 (liftVelocity R (trainProfile T.ψ)) τ =ᶠ[𝓝 y]
      Axi.Nv R (Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) τ := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
    rw [simProfile_liftVelocity_eq_Nv hR0 _ τ hz]
    simp only [Axi.Nv]
    rw [hmer (Axi.chart R τ z) (UnforcedLeray.Short.PartIIIb.Concrete.age_pos_of hR0 hz)]
  rw [(hevU.iteratedFDeriv ℝ j).eq_of_nhds]
  have hs : 0 < Axi.age R y := UnforcedLeray.Short.PartIIIb.Concrete.age_pos_of hR0 hy
  by_cases hfar : Axi.age R y ≤ 1
  · -- Case 1: Early age `Axi.age R y ≤ 1`
    have hnv := Hnv R _ hR1 hΨ τ y hy
    have htermF : ∀ i ∈ I,
        (1 + |Axi.trans R y|) ^ (j + 1) *
          ‖iteratedFDeriv ℝ i (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) (Axi.chart R τ y)‖ ≤
          polyConst (CF i) sumdF ν (ν ^ (-ρ)) := by
      intro i hi
      have hν_i : ν ≤ νF i :=
        hνleF.trans (inv_one_add_le (hνF i)
          (Finset.single_le_sum (f := fun i => 1 / νF i)
            (fun i _ => (one_div_pos.2 (hνF i)).le) hi))
      have hd_i : dF i ≤ sumdF :=
        Finset.single_le_sum (f := dF) (fun _ _ => Nat.zero_le _) hi
      exact (hbdF i ν hν0 hν_i T hT (Axi.chart R τ y) hs hfar).trans
        (polyConst_mono hν0 hc0 le_rfl (hCF i) hd_i)
    have hw : (1 + |Axi.trans R y|) ^ (j + 1) * ∑ i ∈ I,
        ‖iteratedFDeriv ℝ i (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) (Axi.chart R τ y)‖ ≤
        polyConst sumCF sumdF ν (ν ^ (-ρ)) := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum htermF).trans (le_of_eq ?_)
      dsimp [sumCF]
      unfold polyConst
      rw [Finset.sum_mul]
    have h2 : (1 + Axi.age R y) ^ (K + 1) ≤ 2 ^ (K + 1) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    have hearly : ‖iteratedFDeriv ℝ j
        (Axi.Nv R (Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) τ) y‖ ≤
        polyConst C_early sumdF ν (ν ^ (-ρ)) := by
      calc ‖iteratedFDeriv ℝ j
              (Axi.Nv R (Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) τ) y‖
          ≤ Cnv * (1 + Axi.age R y) ^ (K + 1) * ((1 + |Axi.trans R y|) ^ (j + 1) *
              ∑ i ∈ I, ‖iteratedFDeriv ℝ i
                (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2) (Axi.chart R τ y)‖) := hnv
        _ ≤ Cnv * 2 ^ (K + 1) * polyConst sumCF sumdF ν (ν ^ (-ρ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h2 hCnv0) hw (by positivity) (by positivity)
        _ = polyConst C_early sumdF ν (ν ^ (-ρ)) := by
            dsimp [C_early]; unfold polyConst; ring
    exact hearly.trans (polyConst_mono hν0 hc0 (le_add_of_nonneg_right hC_late0)
      (add_nonneg hC_early0 hC_late0) (le_max_left _ _))
  · -- Case 2: Late age `1 < Axi.age R y`
    push Not at hfar
    have hs1 : 1 ≤ Axi.age R y := hfar.le
    have hϱ : Axi.ϱ y ^ 2 ≤ R ^ 2 := by
      have hϱ0 : 0 < Axi.ϱ y ^ 2 := pow_pos (Axi.ϱ_pos hy) 2
      have h1 : 1 < R ^ 2 / Axi.ϱ y ^ 2 := hfar
      rw [lt_div_iff₀ hϱ0] at h1
      linarith
    have hΦN : ContDiffOn ℝ ∞ (heatRemainder ν (UnforcedLeray.Short.PartI.meanCoeff T) N
        (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Ioi 0 ×ˢ univ) :=
      hΨ.sub (ContDiffOn.sum fun l _ => contDiffOn_const.mul (heatTermSmooth ν hν0 l))
    have hBNs := (hP R _ hΦN).1
    have hev : Axi.Nv R (Axi.ringStreamProfile R (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) τ
        =ᶠ[𝓝 y] heatSum ν R (UnforcedLeray.Short.PartI.meanCoeff T) N +
          Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν
            (UnforcedLeray.Short.PartI.meanCoeff T) N
            (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ := by
      filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
      exact Nv_heat_decomp hν0 hR0 _ N hΨ τ hz
    have hNvc : ContDiffAt ℝ j (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν
        (UnforcedLeray.Short.PartI.meanCoeff T) N
        (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y :=
      (((HJ R τ _ hR1 hBNs).1).contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).of_le
        (by exact_mod_cast le_top)
    have hHc : ContDiffAt ℝ j (heatSum ν R (UnforcedLeray.Short.PartI.meanCoeff T) N) y :=
      (contDiff_heatSum ν R _ N).contDiffAt.of_le (by exact_mod_cast le_top)
    rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, iteratedFDeriv_add_apply hHc hNvc]
    refine (norm_add_le _ _).trans ?_
    have h1 := Hh ν hν0 hνleH T hT R hR1 y hϱ
    have h2 := Hnv R _ hR1 hΦN τ y hy
    have hrpow0 : 0 ≤ Axi.age R y ^ (((j + 1 : ℕ) : ℝ) / 2 - N - 3 / 2) :=
      Real.rpow_nonneg hs.le _
    have htermN : ∀ i ∈ I,
        (1 + |Axi.trans R y|) ^ (j + 1) *
          ‖iteratedFDeriv ℝ i (heatRemainder ν (UnforcedLeray.Short.PartI.meanCoeff T) N
            (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Axi.chart R τ y)‖ ≤
          polyConst (CN i) sumdN ν (ν ^ (-ρ)) *
            Axi.age R y ^ (((j + 1 : ℕ) : ℝ) / 2 - N - 3 / 2) := by
      intro i hi
      have hν_i : ν ≤ νN i :=
        hνleN.trans (inv_one_add_le (hνN i)
          (Finset.single_le_sum (f := fun i => 1 / νN i)
            (fun i _ => (one_div_pos.2 (hνN i)).le) hi))
      have hd_i : dN i ≤ sumdN :=
        Finset.single_le_sum (f := dN) (fun _ _ => Nat.zero_le _) hi
      exact (hbdN i ν hν0 hν_i T hT (Axi.chart R τ y) hs1).trans
        (mul_le_mul_of_nonneg_right (polyConst_mono hν0 hc0 le_rfl (hCN i) hd_i) hrpow0)
    have hw : (1 + |Axi.trans R y|) ^ (j + 1) * ∑ i ∈ I,
        ‖iteratedFDeriv ℝ i (heatRemainder ν (UnforcedLeray.Short.PartI.meanCoeff T) N
          (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Axi.chart R τ y)‖ ≤
        polyConst sumCN sumdN ν (ν ^ (-ρ)) *
          Axi.age R y ^ (((j + 1 : ℕ) : ℝ) / 2 - N - 3 / 2) := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum htermN).trans (le_of_eq ?_)
      dsimp [sumCN]
      unfold polyConst
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    have he : ((j + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2 ≤ -((K + 1 : ℕ) : ℝ) := by
      rw [hNdef]; push_cast; linarith
    have hpow : (1 + Axi.age R y) ^ (K + 1) *
        Axi.age R y ^ (((j + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2) ≤ 2 ^ (K + 1) := by
      have h2s : (1 + Axi.age R y) ^ (K + 1) ≤ 2 ^ (K + 1) * Axi.age R y ^ (K + 1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by linarith) (by linarith) _
      have hle1 : Axi.age R y ^ (K + 1) *
          Axi.age R y ^ (((j + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2) ≤ 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hs]
        exact Real.rpow_le_one_of_one_le_of_nonpos hs1 (by push_cast at he ⊢; linarith)
      calc (1 + Axi.age R y) ^ (K + 1) *
              Axi.age R y ^ (((j + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2)
          ≤ 2 ^ (K + 1) * Axi.age R y ^ (K + 1) *
              Axi.age R y ^ (((j + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2) :=
            mul_le_mul_of_nonneg_right h2s hrpow0
        _ = 2 ^ (K + 1) * (Axi.age R y ^ (K + 1) *
              Axi.age R y ^ (((j + 1 : ℕ) : ℝ) / 2 - (N : ℝ) - 3 / 2)) := by ring
        _ ≤ 2 ^ (K + 1) * 1 := mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ = 2 ^ (K + 1) := mul_one _
    have hCnvA : 0 ≤ Cnv * (1 + Axi.age R y) ^ (K + 1) :=
      mul_nonneg hCnv0 (pow_nonneg (by linarith) _)
    have hPCN0 : 0 ≤ polyConst sumCN sumdN ν (ν ^ (-ρ)) :=
      polyConst_nonneg_of hsumCN0 sumdN hν0 hc0
    have hrem : ‖iteratedFDeriv ℝ j
        (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν
          (UnforcedLeray.Short.PartI.meanCoeff T) N
          (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y‖ ≤
        polyConst (Cnv * 2 ^ (K + 1) * sumCN) sumdN ν (ν ^ (-ρ)) := by
      calc ‖iteratedFDeriv ℝ j
              (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν
                (UnforcedLeray.Short.PartI.meanCoeff T) N
                (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y‖
          ≤ Cnv * (1 + Axi.age R y) ^ (K + 1) * ((1 + |Axi.trans R y|) ^ (j + 1) *
              ∑ i ∈ I, ‖iteratedFDeriv ℝ i
                (heatRemainder ν (UnforcedLeray.Short.PartI.meanCoeff T) N
                  (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2)) (Axi.chart R τ y)‖) := h2
        _ ≤ Cnv * (1 + Axi.age R y) ^ (K + 1) *
              (polyConst sumCN sumdN ν (ν ^ (-ρ)) *
                Axi.age R y ^ (((j + 1 : ℕ) : ℝ) / 2 - N - 3 / 2)) :=
            mul_le_mul_of_nonneg_left hw hCnvA
        _ = Cnv * polyConst sumCN sumdN ν (ν ^ (-ρ)) *
              ((1 + Axi.age R y) ^ (K + 1) *
                Axi.age R y ^ (((j + 1 : ℕ) : ℝ) / 2 - N - 3 / 2)) := by ring
        _ ≤ Cnv * polyConst sumCN sumdN ν (ν ^ (-ρ)) * 2 ^ (K + 1) :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg hCnv0 hPCN0)
        _ = polyConst (Cnv * 2 ^ (K + 1) * sumCN) sumdN ν (ν ^ (-ρ)) := by
            unfold polyConst; ring
    have hlate : ‖iteratedFDeriv ℝ j
          (heatSum ν R (UnforcedLeray.Short.PartI.meanCoeff T) N) y‖ +
        ‖iteratedFDeriv ℝ j
          (Axi.Nv R (Axi.ringStreamProfile R (heatRemainder ν
            (UnforcedLeray.Short.PartI.meanCoeff T) N
            (fun x : ℝ × (ℝ × ℝ) => T.ψ x.1 x.2))) τ) y‖ ≤
        polyConst C_late (max dH sumdN) ν (ν ^ (-ρ)) :=
      (add_le_add h1 hrem).trans
        (polyConst_add_le hCH (by positivity) dH sumdN hν0 hc0)
    exact hlate.trans (polyConst_mono hν0 hc0 (le_add_of_nonneg_left hC_early0)
      (add_nonneg hC_early0 hC_late0) (le_max_right _ _))

/-- **`PartII-a:R07`: bounded spatial derivatives of the similarity profile** (`RingBoundedDerivs`,
`Short/PartII-a/StatementsRing.lean:217`). -/
theorem ringBoundedDerivs : RingBoundedDerivs := by
  have hOFluct : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOMean : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform hOFluct
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hOFluct hOMean
  have hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail :=
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay :=
    UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hOFluct hOv
  have hME : UnforcedLeray.Short.PartI.TrainMeanExpansion :=
    UnforcedLeray.Short.PartI.trainMeanExpansion_proof hTails hFD
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  intro ρ k hρ
  obtain ⟨ν_ax, hν_ax, H_ax⟩ := ringAxisSmooth ρ hρ
  have hex : ∀ j : ℕ, ∃ (ν₀ C : ℝ) (d : ℕ), 0 < ν₀ ∧ 0 ≤ C ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ ψ pr : ProfilePoint → ℝ, IsExactPlanarTrain ν (ν ^ (-ρ)) ψ pr →
          ∀ R : ℝ, 2 ≤ R → ∀ (τ : ℝ) (y : Space), Axi.ϱ y ≠ 0 →
            ‖iteratedFDeriv ℝ j (simProfile 1 (liftVelocity R ψ) τ) y‖ ≤
              polyConst C d ν (ν ^ (-ρ)) :=
    fun j => ringOffAxisDerivBdd hFD hME hρ j
  choose νb Cb db hνb hCb H_off using hex
  set J := Finset.range (k + 1)
  have hSνb : 0 ≤ ∑ j ∈ J, 1 / νb j :=
    Finset.sum_nonneg fun j _ => (one_div_pos.2 (hνb j)).le
  set ν₀_b := 1 / (1 + ∑ j ∈ J, 1 / νb j)
  set ν₀ := min ν_ax ν₀_b
  have hν₀ : 0 < ν₀ := lt_min hν_ax (inv_one_add_pos hSνb)
  set C := ∑ j ∈ J, Cb j
  set d := ∑ j ∈ J, db j
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => hCb j
  refine ⟨ν₀, hν₀, C, d, fun ν hν ψ p hpr R hR => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν_lt_ax : ν < ν_ax := lt_of_lt_of_le hν.2 (min_le_left _ _)
  have hν_le_b : ν ≤ ν₀_b := hν.2.le.trans (min_le_right _ _)
  obtain ⟨u, π, hu, -, hagree⟩ := H_ax ν ⟨hν0, hν_lt_ax⟩ ψ p hpr R hR
  set U : ℝ → Space → Space := fun τ y =>
    Real.exp (τ / 2) • u (Real.exp τ, Real.exp (τ / 2) • y) with hUdef
  have hsm : ∀ τ, ContDiff ℝ ∞ (U τ) := by
    intro τ
    have h1 : ContDiff ℝ ∞ (fun y : Space => (Real.exp τ, Real.exp (τ / 2) • y)) :=
      contDiff_const.prodMk (contDiff_const_smul _)
    have h2 : ContDiff ℝ ∞ (fun y : Space => u (Real.exp τ, Real.exp (τ / 2) • y)) := by
      rw [← contDiffOn_univ]
      exact hu.comp h1.contDiffOn (fun y _ => Real.exp_pos τ)
    exact (contDiff_const (c := Real.exp (τ / 2))).smul h2
  have hoff : ∀ τ (y : Space), Axi.ϱ y ≠ 0 →
      U τ y = simProfile 1 (liftVelocity R ψ) τ y := by
    intro τ y hy
    have hx : Real.exp (τ / 2) • y ∉ Axi.axis := by
      rw [← varrho_ne_zero_iff, Axi.ϱ_smul]
      exact mul_ne_zero (by simp [abs_of_pos (Real.exp_pos _)]) hy
    simp only [hUdef, simProfile]
    rw [(hagree _ (Real.exp_pos τ) _ hx).1, pow_one]
  refine ⟨U, hsm, hoff, fun j hj τ y => ?_⟩
  have hjJ : j ∈ J := Finset.mem_range.2 (Nat.lt_succ_of_le hj)
  have hν_j : ν ≤ νb j :=
    hν_le_b.trans (inv_one_add_le (hνb j)
      (Finset.single_le_sum (f := fun j => 1 / νb j)
        (fun j _ => (one_div_pos.2 (hνb j)).le) hjJ))
  have hC_j : Cb j ≤ C := Finset.single_le_sum (f := Cb) (fun i _ => hCb i) hjJ
  have hd_j : db j ≤ d := Finset.single_le_sum (f := db) (fun _ _ => Nat.zero_le _) hjJ
  have hc0 : 0 < ν ^ (-ρ) := Real.rpow_pos_of_pos hν0 _
  have hP_mono : polyConst (Cb j) (db j) ν (ν ^ (-ρ)) ≤ polyConst C d ν (ν ^ (-ρ)) :=
    polyConst_mono hν0 hc0 hC_j hC0 hd_j
  have hopen : IsOpen {z : Space | Axi.ϱ z ≠ 0} :=
    isOpen_ne_fun Axi.continuous_ϱ continuous_const
  have hcl : IsClosed {z : Space | ‖iteratedFDeriv ℝ j (U τ) z‖ ≤ polyConst C d ν (ν ^ (-ρ))} :=
    isClosed_le ((hsm τ).continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm
      continuous_const
  have hdense : Dense {z : Space | Axi.ϱ z ≠ 0} := by
    refine (UnforcedLeray.Cons.C03.dense_compl_axis).mono ?_
    intro z hz
    exact varrho_ne_zero_iff.2 hz
  have hsub : {z : Space | Axi.ϱ z ≠ 0} ⊆
      {z : Space | ‖iteratedFDeriv ℝ j (U τ) z‖ ≤ polyConst C d ν (ν ^ (-ρ))} := by
    intro z hz
    have hev : U τ =ᶠ[𝓝 z] simProfile 1 (liftVelocity R ψ) τ :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) (fun w hw => hoff τ w hw)
    show ‖iteratedFDeriv ℝ j (U τ) z‖ ≤ polyConst C d ν (ν ^ (-ρ))
    rw [(hev.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    exact (H_off j ν hν0 hν_j ψ p hpr R hR τ z hz).trans hP_mono
  exact (hcl.closure_subset_iff.2 hsub) (hdense y)

end UnforcedLeray.Short.PartIIa
