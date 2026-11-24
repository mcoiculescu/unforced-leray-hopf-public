import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.SourceFacts
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Of
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.PartIIIa.T06_ScalingJa
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L4

/-!


Source of record: `the November 2 reference manuscript` (73 pages), lines
4376-4380 ("the endpoint heat-scaling maps have uniform norms on `a ≤ 1 + Σ`, so the frozen
vectors and dual functionals are bounded uniformly on the band") and 2894-2899 (uniform frame
facts).

Proves `frozenPairBoundedActual`: for every actual flat sequence `S`, the frozen pair `(S n).pk.q`
and its dual `(S n).pk.ell` have norms bounded uniformly in large `n` and `0 ≤ s ≤ 2 / ν_n`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF FlatSettingInst

/-- The weighted norm of the planar function of `w ∈ X_{m,c}` is the norm of `w`. -/
private theorem xNorm_xFn_eq {c m : ℝ} [Fact (1 < m)] (w : Xmc c m) :
    IIIa.xNorm c m (xFn w) = ENNReal.ofReal ‖w‖ := by
  have h1 : ‖w‖ = ‖(w : XAmb c m)‖ := (Submodule.coe_norm w).symm
  rw [h1, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top (w : XAmb c m)).ne]
  rfl

/-- Uniform norm bound for `q j s` of a pinned `FrozenPair` under `IIIa.PerFrameFacts`. -/
private theorem norm_pair_q_le {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ} [Fact (1 < m)]
    (hm : 8 < m) (hν0 : 0 < ν) (hb : 0 < b) (hνb : ν ≤ 1 / (3 * b))
    (hPF : IIIa.PerFrameFacts κ ν m b K) (P : FrozenPair κ ν (cOf ν) m) (j : Bool) (s : ℝ) :
    ‖P.q j s‖ ≤ (3 : ℝ) ^ ((m - 3) / 2) * max K 0 := by
  let c := cOf ν
  have hc0 : 0 < c := cOf_pos hν0
  have hcR : c = ν ^ (-2 : ℝ) := by
    change cOf ν = ν ^ (-2 : ℝ)
    rw [cOf, Real.rpow_neg hν0.le, Real.rpow_two]
  have ha1 : 1 ≤ bandA ν s := Pair.one_le_bandA hν0 s
  have ha0 : 0 < bandA ν s := Pair.bandA_pos hν0 s
  have ha3 : bandA ν s ≤ 3 := Pair.bandA_le_three hν0 s
  have hd0 : 0 < bandD ν c s := Pair.bandD_pos hν0 hc0 s
  have hdc : bandD ν c s * Real.sqrt (bandA ν s) = c :=
    div_mul_cancel₀ c (Real.sqrt_pos.2 ha0).ne'
  have hq1 : ENNReal.ofReal ‖P.q j s‖ = IIIa.xNorm c m (xFn (P.q j s)) :=
    (xNorm_xFn_eq (P.q j s)).symm
  have hq2 : IIIa.xNorm c m (xFn (P.q j s)) = IIIa.xNorm c m (frozenQ κ ν c j s) :=
    eLpNorm_congr_ae (ae_cellMeasure_of_ae_cell (P.q_pin j s))
  have hmeas : Measurable (IIIa.perE κ (bandD ν c s) (pmIdx j)) :=
    (IIIa.perE_continuous_aux κ hd0 (pmIdx j)).measurable
  have hsc := IIIa.scalingJa m (by linarith : 0 ≤ m) (bandA ν s) (bandD ν c s) ha1 hd0
    (IIIa.perE κ (bandD ν c s) (pmIdx j)) hmeas
  rw [hdc] at hsc
  have hE := hPF.2.1 (bandAge ν s) (Pair.bandAge_nonneg s)
    (Pair.le_clockTheta_bandAge hν0 hb hνb s) (pmIdx j)
  rw [← hcR] at hE
  have hpow : bandA ν s ^ ((m - 3) / 2) ≤ (3 : ℝ) ^ ((m - 3) / 2) :=
    Real.rpow_le_rpow ha0.le ha3 (by linarith)
  have hK : ENNReal.ofReal K ≤ ENNReal.ofReal (max K 0) :=
    ENNReal.ofReal_le_ofReal (le_max_left K 0)
  have htot : ENNReal.ofReal ‖P.q j s‖ ≤
      ENNReal.ofReal ((3 : ℝ) ^ ((m - 3) / 2) * max K 0) := by
    calc ENNReal.ofReal ‖P.q j s‖
        = IIIa.xNorm c m (frozenQ κ ν c j s) := hq1.trans hq2
      _ ≤ ENNReal.ofReal (bandA ν s ^ ((m - 3) / 2)) *
            IIIa.xNorm (bandD ν c s) m (IIIa.perE κ (bandD ν c s) (pmIdx j)) := hsc
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ ((m - 3) / 2)) * ENNReal.ofReal (max K 0) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) (hE.trans hK)
      _ = ENNReal.ofReal ((3 : ℝ) ^ ((m - 3) / 2) * max K 0) :=
            (ENNReal.ofReal_mul (by positivity)).symm
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 htot

/-- Uniform operator-norm bound for `ell j s` of a pinned `FrozenPair` under `IIIa.PerFrameFacts`. -/
private theorem norm_pair_ell_le {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ} [Fact (1 < m)]
    (_hm : 8 < m) (hν0 : 0 < ν) (hb : 0 < b) (hνb : ν ≤ 1 / (3 * b))
    (hPF : IIIa.PerFrameFacts κ ν m b K) (P : FrozenPair κ ν (cOf ν) m) (j : Bool) (s : ℝ) :
    ‖P.ell j s‖ ≤ max K 0 * (3 : ℝ) ^ ((3 : ℝ) / 2) := by
  let c := cOf ν
  have hcR : c = ν ^ (-2 : ℝ) := by
    change cOf ν = ν ^ (-2 : ℝ)
    rw [cOf, Real.rpow_neg hν0.le, Real.rpow_two]
  have ha1 : 1 ≤ bandA ν s := Pair.one_le_bandA hν0 s
  have ha0 : 0 < bandA ν s := Pair.bandA_pos hν0 s
  have ha3 : bandA ν s ≤ 3 := Pair.bandA_le_three hν0 s
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have h1 : P.ell j s x = frozenEll κ ν c j s (xFn x) := P.ell_pin j s x
  have hL := hPF.2.2 (bandAge ν s) (Pair.bandAge_nonneg s)
    (Pair.le_clockTheta_bandAge hν0 hb hνb s) (pmIdx j) (IIIa.JscaleInv (bandA ν s) (xFn x))
  have hL' : ENNReal.ofReal ‖frozenEll κ ν c j s (xFn x)‖ ≤
      ENNReal.ofReal K * IIIa.xNorm (bandD ν c s) m (IIIa.JscaleInv (bandA ν s) (xFn x)) := by
    unfold IIIa.movingCell at hL
    unfold frozenEll bandD bandA
    rwa [← hcR] at hL
  have hJ := IIIa.xNorm_JscaleInv_le c m (bandA ν s) (by linarith : 0 ≤ m) ha1
    (xFn x) (xFn_memLp x)
  rw [xNorm_xFn_eq x] at hJ
  have hpow : bandA ν s ^ ((3 : ℝ) / 2) ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow ha0.le ha3 (by norm_num)
  have hK : ENNReal.ofReal K ≤ ENNReal.ofReal (max K 0) :=
    ENNReal.ofReal_le_ofReal (le_max_left K 0)
  have htot : ENNReal.ofReal ‖P.ell j s x‖ ≤
      ENNReal.ofReal (max K 0 * (3 : ℝ) ^ ((3 : ℝ) / 2) * ‖x‖) := by
    rw [h1]
    calc ENNReal.ofReal ‖frozenEll κ ν c j s (xFn x)‖
        ≤ ENNReal.ofReal K *
            IIIa.xNorm (bandD ν c s) m (IIIa.JscaleInv (bandA ν s) (xFn x)) := hL'
      _ ≤ ENNReal.ofReal (max K 0) *
            (ENNReal.ofReal (bandA ν s ^ ((3 : ℝ) / 2)) * ENNReal.ofReal ‖x‖) :=
          mul_le_mul' hK hJ
      _ ≤ ENNReal.ofReal (max K 0) *
            (ENNReal.ofReal ((3 : ℝ) ^ ((3 : ℝ) / 2)) * ENNReal.ofReal ‖x‖) :=
          mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl)
      _ = ENNReal.ofReal (max K 0 * (3 : ℝ) ^ ((3 : ℝ) / 2) * ‖x‖) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            mul_assoc]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 htot

/-- **Frozen pair bounded on the finite band** (source 4376-4380). -/
theorem frozenPairBoundedActual (D : SeqData) : G1.FrozenPairBoundedActual D := by
  intro dm dp hD κ hκ m hfact hm S hS
  obtain ⟨K, b₀, hb₀⟩ := IIIa.perFrameFactsAll κ hκ.1 m hm
  set b := max b₀ 1
  have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨ν₁, hν₁, hPF⟩ := hb₀ b (le_max_left _ _)
  set ν_max := min ν₁ (1 / (3 * b))
  have hν_max : 0 < ν_max := lt_min hν₁ (by positivity)
  have hlim : Tendsto (nu D) atTop (𝓝 0) := retNu_tendsto D.σ₀ hD.omega_ne
  have hev_nu : ∀ᶠ n : ℕ in atTop, nu D n ≤ ν_max :=
    hlim.eventually (Iic_mem_nhds hν_max)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hS.and hev_nu)
  refine ⟨N0, max ((3 : ℝ) ^ ((m - 3) / 2) * max K 0) (max K 0 * (3 : ℝ) ^ ((3 : ℝ) / 2)),
    fun n hn s _hs j => ?_⟩
  obtain ⟨⟨FI, hFI⟩, hνn⟩ := hN0 n hn
  have hν0 : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have hνle : nu D n ≤ ν₁ := hνn.trans (min_le_left _ _)
  have hνb : nu D n ≤ 1 / (3 * b) := hνn.trans (min_le_right _ _)
  have hPFn : IIIa.PerFrameFacts κ (nu D n) m b K := hPF (nu D n) ⟨hν0, hνle⟩
  rw [hFI]
  change ‖FI.pair.q j s‖ ≤ _ ∧ ‖FI.pair.ell j s‖ ≤ _
  exact ⟨(norm_pair_q_le hm hν0 hb hνb hPFn FI.pair j s).trans (le_max_left _ _),
    (norm_pair_ell_le hm hν0 hb hνb hPFn FI.pair j s).trans (le_max_right _ _)⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif
