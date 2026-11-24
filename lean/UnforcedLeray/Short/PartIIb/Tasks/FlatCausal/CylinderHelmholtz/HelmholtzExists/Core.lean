import UnforcedLeray.Short.PartIIb.Sub.T12_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists.Pair
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists.Trunc
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists.Diff
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists.Weights

/-!
# Existence of the cylinder Helmholtz decomposition for general `F ∈ L^r`

`cyl_exists_core`: given the nice-case theorem (`hnice`), the uniqueness leaf, and `CylOfPlaneProps`,
every `c`-periodic `F ∈ L^r(avgμ c)` has a cylinder Helmholtz companion with the bound `C`.

Proof: `F_n = truncF n F` (bounded, in `|η| ≤ n`, periodic, `F_n → F` in `L^r`). Let `G_n` be the
nice-case companion of `F_n`. By uniqueness, `G_n - G_m` is the nice-case companion of `F_n - F_m`,
so `‖G_n - G_m‖_r ≤ C ‖F_n - F_m‖_r`. A subsequence `G_{M k}` is Cauchy with summable bounds, so it
converges a.e. and in `L^r`; the pointwise limit `Gl` (a `limUnder`, periodic because each `G_n` is)
satisfies the three conditions of `IsCylHelmholtz` by passing to the limit in the pairings
(`cylPair_tendsto`) and the bound by the triangle inequality.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

set_option maxHeartbeats 1000000 in
theorem cyl_exists_core (hU : CylHelmholtzUnique) (hCOP : CylOfPlaneProps) {r C : ℝ} (hr : 1 < r)
    (hC : 0 < C)
    (hnice : ∀ c : ℝ, 0 < c → ∀ F : ℝ × ℝ → CMerid, CylLp c r F → CylLp c 2 F →
      ∃ G : ℝ × ℝ → CMerid, CylLp c r G ∧ IsPlaneHelmholtz F G ∧
        eLpNorm G (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
          ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
    {c : ℝ} (hc : 0 < c) (F : ℝ × ℝ → CMerid) (hF : CylLp c r F) :
    ∃ G : ℝ × ℝ → CMerid, IsCylHelmholtz c r F G ∧
      eLpNorm G (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
  have hr0 : 0 < r := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr.le
  have hnc := hnice c hc
  set μ := UnforcedLeray.Cyl.avgμ c with hμ
  have hFr : MemLp F (ENNReal.ofReal r) μ := hF.2
  have hTper : ∀ n : ℕ, ∀ z : ℝ × ℝ, truncF n F (z.1 + c, z.2) = truncF n F z :=
    fun n => truncF_periodic hF.1 n
  have hTL : ∀ (n : ℕ) (p : ℝ≥0∞), MemLp (truncF n F) p μ :=
    fun n p => memLp_truncF hc n hFr.1 p
  have hTcylr : ∀ n : ℕ, CylLp c r (truncF n F) := fun n => ⟨hTper n, hTL n _⟩
  have hTcyl2 : ∀ n : ℕ, CylLp c 2 (truncF n F) := fun n => ⟨hTper n, hTL n _⟩
  have ha : Tendsto (fun n : ℕ => eLpNorm (truncF n F - F) (ENNReal.ofReal r) μ) atTop (𝓝 0) :=
    tendsto_truncF_Lr hc hr hFr
  -- nice companions of the truncations
  have hGex : ∀ n : ℕ, ∃ G : ℝ × ℝ → CMerid, IsCylHelmholtz c r (truncF n F) G ∧
      eLpNorm G (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal C * eLpNorm (truncF n F) (ENNReal.ofReal r) μ :=
    fun n => cylHelmholtz_of_nice hCOP hc hr hnc (truncF n F) (hTcylr n) (hTcyl2 n)
  choose G hG hGb using hGex
  -- Cauchy estimate through uniqueness
  have hcb : ∀ n m : ℕ, eLpNorm (G n - G m) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal C * eLpNorm (truncF n F - truncF m F) (ENNReal.ofReal r) μ := by
    intro n m
    obtain ⟨G', h', hb'⟩ := cylHelmholtz_of_nice hCOP hc hr hnc (truncF n F - truncF m F)
      (cylLp_sub (hTcylr n) (hTcylr m)) (cylLp_sub (hTcyl2 n) (hTcyl2 m))
    rw [eLpNorm_congr_ae (cyl_diff_ae_eq hU hc hr (hG n) (hG m) h')]
    exact hb'
  have hsplit : ∀ n m : ℕ, eLpNorm (truncF n F - truncF m F) (ENNReal.ofReal r) μ ≤
      eLpNorm (truncF n F - F) (ENNReal.ofReal r) μ +
        eLpNorm (truncF m F - F) (ENNReal.ofReal r) μ := by
    intro n m
    have e : truncF n F - truncF m F = (truncF n F - F) - (truncF m F - F) := by abel
    rw [e]
    exact eLpNorm_sub_le
      ((hTL n (ENNReal.ofReal r)).aestronglyMeasurable.sub hFr.aestronglyMeasurable)
      ((hTL m (ENNReal.ofReal r)).aestronglyMeasurable.sub hFr.aestronglyMeasurable) hp1
  -- thresholds
  have hthr : ∀ k : ℕ, ∃ T : ℕ, ∀ n m : ℕ, T ≤ n → T ≤ m →
      eLpNorm (G n - G m) (ENNReal.ofReal r) μ ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have hε : (2⁻¹ : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
    have hden : (2 * ENNReal.ofReal C) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top
    have hδ : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ k / (2 * ENNReal.ofReal C) :=
      ENNReal.div_pos hε hden
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (ENNReal.tendsto_nhds_zero.1 ha _ hδ)
    refine ⟨T, fun n m hn hm => ?_⟩
    have h1 := hT n hn
    have h2 := hT m hm
    calc eLpNorm (G n - G m) (ENNReal.ofReal r) μ
        ≤ ENNReal.ofReal C * eLpNorm (truncF n F - truncF m F) (ENNReal.ofReal r) μ := hcb n m
      _ ≤ ENNReal.ofReal C * (eLpNorm (truncF n F - F) (ENNReal.ofReal r) μ +
            eLpNorm (truncF m F - F) (ENNReal.ofReal r) μ) := by
          gcongr
          exact hsplit n m
      _ ≤ ENNReal.ofReal C * ((2⁻¹ : ℝ≥0∞) ^ k / (2 * ENNReal.ofReal C) +
            (2⁻¹ : ℝ≥0∞) ^ k / (2 * ENNReal.ofReal C)) := by
          gcongr
      _ = (2 * ENNReal.ofReal C) * ((2⁻¹ : ℝ≥0∞) ^ k / (2 * ENNReal.ofReal C)) := by
          rw [← two_mul, ← mul_assoc, mul_comm (ENNReal.ofReal C) 2]
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ k := ENNReal.mul_div_le
  -- subsequence
  choose Tk hTk using hthr
  obtain ⟨M, hM⟩ : ∃ M : ℕ → ℕ, ∀ k, M k = (∑ j ∈ Finset.range (k + 1), Tk j) + k :=
    ⟨fun k => (∑ j ∈ Finset.range (k + 1), Tk j) + k, fun k => rfl⟩
  have hTM : ∀ k, Tk k ≤ M k := by
    intro k
    rw [hM k]
    have := Finset.single_le_sum (f := Tk) (fun j _ => Nat.zero_le _)
      (Finset.self_mem_range_succ k)
    omega
  have hMk : ∀ k, k ≤ M k := by
    intro k
    rw [hM k]
    omega
  have hMmono : ∀ N n : ℕ, N ≤ n → M N ≤ M n := by
    intro N n h
    rw [hM N, hM n]
    have := Finset.sum_le_sum_of_subset (f := Tk)
      (Finset.range_mono (by omega : N + 1 ≤ n + 1))
    omega
  have hlt : ∀ N : ℕ, (2⁻¹ : ℝ≥0∞) ^ N < 2 * (2⁻¹ : ℝ≥0∞) ^ N := by
    intro N
    rw [two_mul]
    exact ENNReal.lt_add_right (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))
      (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))
  have hcau : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (G (M n) - G (M m)) (ENNReal.ofReal r) μ < 2 * (2⁻¹ : ℝ≥0∞) ^ N := by
    intro N n m hn hm
    exact lt_of_le_of_lt (hTk N (M n) (M m) ((hTM N).trans (hMmono N n hn))
      ((hTM N).trans (hMmono N m hm))) (hlt N)
  have hsum : ∑' N : ℕ, 2 * (2⁻¹ : ℝ≥0∞) ^ N ≠ ⊤ := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofNat_ne_top
  have hGmeas : ∀ k, AEStronglyMeasurable (G (M k)) μ :=
    fun k => (hG (M k)).1.2.aestronglyMeasurable
  have hae := MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm (f := fun k => G (M k))
    (p := ENNReal.ofReal r) hGmeas hp1 (B := fun N : ℕ => 2 * (2⁻¹ : ℝ≥0∞) ^ N) hsum hcau
  -- the a.e. limit, periodic by construction
  obtain ⟨Gl, hGl⟩ : ∃ Gl : ℝ × ℝ → CMerid, ∀ x, Gl x = limUnder atTop (fun k => G (M k) x) :=
    ⟨fun x => limUnder atTop (fun k => G (M k) x), fun x => rfl⟩
  have hlim_ae : ∀ᵐ x ∂μ, Tendsto (fun k => G (M k) x) atTop (𝓝 (Gl x)) :=
    hae.mono fun x hx => by
      rw [hGl]
      exact tendsto_nhds_limUnder hx
  have hGl_meas : AEStronglyMeasurable Gl μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hGmeas hlim_ae
  have hL_tend : Tendsto (fun k => eLpNorm (G (M k) - Gl) (ENNReal.ofReal r) μ) atTop (𝓝 0) :=
    MeasureTheory.Lp.cauchy_tendsto_of_tendsto hGmeas Gl hsum hcau hlim_ae
  have hL_mem : MemLp Gl (ENNReal.ofReal r) μ :=
    MeasureTheory.Lp.memLp_of_cauchy_tendsto hp1 (fun k => (hG (M k)).1.2) Gl hGl_meas hL_tend
  have hGper : ∀ k : ℕ, ∀ z : ℝ × ℝ, G (M k) (z.1 + c, z.2) = G (M k) z :=
    fun k z => (hG (M k)).1.1 z
  have hLper : ∀ z : ℝ × ℝ, Gl (z.1 + c, z.2) = Gl z := by
    intro z
    rw [hGl, hGl]
    simp only [hGper]
  have hGLcyl : CylLp c r Gl := ⟨hLper, hL_mem⟩
  -- weak conditions
  have hweak : ∀ φ : ℝ × ℝ → ℝ, CylTest c φ →
      Integrable (fun z => Gl z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
        Gl z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) μ ∧
      ∫ z, (Gl z 0 * (fderiv ℝ φ z (1, 0) : ℂ) + Gl z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) ∂μ = 0 := by
    intro φ hφ
    obtain ⟨hcont, ⟨Mb, hMb⟩, ⟨Lb, hLb⟩⟩ := cylTest_weights hc hφ
    have hfeq : (fun z => Gl z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
        Gl z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) = fun z => cylPair (testWeights φ) Gl z := by
      funext z
      simp [cylPair, testWeights, Fin.sum_univ_two]
    have hfeqk : ∀ k : ℕ, (fun z => G (M k) z 0 * (fderiv ℝ φ z (1, 0) : ℂ) +
        G (M k) z 1 * (fderiv ℝ φ z (0, 1) : ℂ)) = fun z => cylPair (testWeights φ) (G (M k)) z := by
      intro k
      funext z
      simp [cylPair, testWeights, Fin.sum_univ_two]
    have hint : Integrable (cylPair (testWeights φ) Gl) μ :=
      cylPair_integrable hc hr hcont hMb hLb hL_mem
    have hz : ∀ k : ℕ, ∫ z, cylPair (testWeights φ) (G (M k)) z ∂μ = 0 := by
      intro k
      have := (hG (M k)).2.1 φ hφ
      rw [← hfeqk k]
      exact this.2
    have hT := cylPair_tendsto hc hr hcont hMb hLb (H := fun k => G (M k)) (H₀ := Gl)
      (fun k => (hG (M k)).1.2) hL_mem hL_tend
    have hconst : Tendsto (fun k => ∫ z, cylPair (testWeights φ) (G (M k)) z ∂μ) atTop
        (𝓝 0) := by
      simp only [hz]
      exact tendsto_const_nhds
    have hzero : ∫ z, cylPair (testWeights φ) Gl z ∂μ = 0 := tendsto_nhds_unique hT hconst
    rw [hfeq]
    exact ⟨hint, hzero⟩
  -- solenoidal conditions
  have hsol : ∀ Ψ : ℝ × ℝ → Fin 2 → ℝ, CylSolTest c Ψ →
      Integrable (fun z => ∑ i : Fin 2, (F z i - Gl z i) * (Ψ z i : ℂ)) μ ∧
      ∫ z, ∑ i : Fin 2, (F z i - Gl z i) * (Ψ z i : ℂ) ∂μ = 0 := by
    intro Ψ hΨ
    obtain ⟨hcont, ⟨Mb, hMb⟩, ⟨Lb, hLb⟩⟩ := cylSol_weights hc hΨ
    have hfeq : (fun z => ∑ i : Fin 2, (F z i - Gl z i) * (Ψ z i : ℂ)) =
        fun z => cylPair (fun i z => (Ψ z i : ℂ)) (F - Gl) z := by
      funext z
      simp [cylPair, Fin.sum_univ_two]
    have hint : Integrable (cylPair (fun i z => (Ψ z i : ℂ)) (F - Gl)) μ :=
      cylPair_integrable hc hr (w := fun i z => (Ψ z i : ℂ)) hcont hMb hLb (hFr.sub hL_mem)
    have hzero_k : ∀ k : ℕ, ∫ z, cylPair (fun i z => (Ψ z i : ℂ))
        (truncF (M k) F - G (M k)) z ∂μ = 0 := by
      intro k
      have := (hG (M k)).2.2 Ψ hΨ
      have e : (fun z => cylPair (fun i z => (Ψ z i : ℂ)) (truncF (M k) F - G (M k)) z) =
          fun z => ∑ i : Fin 2, (truncF (M k) F z i - G (M k) z i) * (Ψ z i : ℂ) := by
        funext z
        simp [cylPair, Fin.sum_univ_two]
      rw [e]
      exact this.2
    have hlimS : Tendsto (fun k => eLpNorm ((truncF (M k) F - G (M k)) - (F - Gl))
        (ENNReal.ofReal r) μ) atTop (𝓝 0) := by
      have hA : Tendsto (fun k => eLpNorm (truncF (M k) F - F) (ENNReal.ofReal r) μ) atTop
          (𝓝 0) :=
        ha.comp (tendsto_atTop_mono hMk tendsto_id)
      have hsq := hA.add hL_tend
      rw [add_zero] at hsq
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq
        (fun k => (zero_le : (0 : ℝ≥0∞) ≤ _)) (fun k => ?_)
      have e : (truncF (M k) F - G (M k)) - (F - Gl) =
          (truncF (M k) F - F) - (G (M k) - Gl) := by abel
      rw [e]
      exact eLpNorm_sub_le
        ((hTL (M k) (ENNReal.ofReal r)).aestronglyMeasurable.sub hFr.aestronglyMeasurable)
        ((hG (M k)).1.2.aestronglyMeasurable.sub hGl_meas) hp1
    have hT := cylPair_tendsto hc hr (w := fun i z => (Ψ z i : ℂ)) hcont hMb hLb
      (H := fun k => truncF (M k) F - G (M k)) (H₀ := F - Gl)
      (fun k => (hTL (M k) (ENNReal.ofReal r)).sub (hG (M k)).1.2) (hFr.sub hL_mem) hlimS
    have hconst : Tendsto (fun k => ∫ z, cylPair (fun i z => (Ψ z i : ℂ))
        (truncF (M k) F - G (M k)) z ∂μ) atTop (𝓝 0) := by
      simp only [hzero_k]
      exact tendsto_const_nhds
    have hzero : ∫ z, cylPair (fun i z => (Ψ z i : ℂ)) (F - Gl) z ∂μ = 0 :=
      tendsto_nhds_unique hT hconst
    rw [hfeq]
    exact ⟨hint, hzero⟩
  -- the bound
  have hbound : eLpNorm Gl (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) μ := by
    have hgk : ∀ k : ℕ, eLpNorm (G (M k)) (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) μ := by
      intro k
      refine (hGb (M k)).trans ?_
      gcongr
      exact eLpNorm_mono (fun z => norm_truncF_le (M k) F z)
    have hsp : ∀ k : ℕ, eLpNorm Gl (ENNReal.ofReal r) μ ≤
        eLpNorm (G (M k) - Gl) (ENNReal.ofReal r) μ + eLpNorm (G (M k)) (ENNReal.ofReal r) μ := by
      intro k
      have e : Gl = (Gl - G (M k)) + G (M k) := by abel
      have hneg : eLpNorm (Gl - G (M k)) (ENNReal.ofReal r) μ =
          eLpNorm (G (M k) - Gl) (ENNReal.ofReal r) μ := by
        rw [← neg_sub, eLpNorm_neg]
      calc eLpNorm Gl (ENNReal.ofReal r) μ
          = eLpNorm ((Gl - G (M k)) + G (M k)) (ENNReal.ofReal r) μ := by rw [← e]
        _ ≤ eLpNorm (Gl - G (M k)) (ENNReal.ofReal r) μ +
            eLpNorm (G (M k)) (ENNReal.ofReal r) μ :=
          eLpNorm_add_le (hGl_meas.sub (hGmeas k)) (hGmeas k) hp1
        _ = eLpNorm (G (M k) - Gl) (ENNReal.ofReal r) μ + eLpNorm (G (M k)) (ENNReal.ofReal r) μ := by
          rw [hneg]
    have hT2 : Tendsto (fun k : ℕ => eLpNorm (G (M k) - Gl) (ENNReal.ofReal r) μ +
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) μ) atTop
        (𝓝 (0 + ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) μ)) :=
      hL_tend.add tendsto_const_nhds
    rw [zero_add] at hT2
    have hev : ∀ k : ℕ, eLpNorm Gl (ENNReal.ofReal r) μ ≤
        eLpNorm (G (M k) - Gl) (ENNReal.ofReal r) μ +
          ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal r) μ := fun k =>
      (hsp k).trans (by gcongr <;> exact hgk k)
    exact ge_of_tendsto hT2 (Filter.Eventually.of_forall hev)
  exact ⟨Gl, ⟨hGLcyl, hweak, hsol⟩, hbound⟩

end UnforcedLeray.Short.IIb
