import UnforcedLeray.Short.PartIIa.Tasks.R07BoundedDerivs.JetUnif
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.SqrtFrameJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.SqrtFrameJets.InvRho
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_7.InletDecay

/-!
# Ring-lift jets keeping the amplitude `√s` (copy of `RawAndInletL4/SqrtLift.lean` of `PartII-b:S2/3`, helper for `PartII-b:S2/1/4`)

Source of record: `the November 2 reference manuscript`, lines 2543-2547
("in the large-radius region their unprojected derivatives are bounded by
`C_{k,N} ϱ^{-3-k}(1+|y_3|/ϱ)^{-N}`") and 2607-2608 (inverse-distance bounds give `D^jV ∈ C_per L^4`).

`RingLiftPtJet` bounds `D^j N_v b` by `C (1+s)^k (1+|η|)^j ∑_{l ≤ j} ‖D^l b‖`; here the amplitude jets
`‖D^i √s‖ = R ‖D^i ϱ⁻¹‖ ≤ C R ϱ^{-1-i} = C √s ϱ^{-i}` (`varrho_inv_jet`) keep the factor `√s`, so
`‖D^j N_v b‖ ≤ C √s (1+s)^k (1+|η|)^j ∑_{l ≤ j} ‖D^l b‖` (`ringLiftPtJetSqrt`), and for the ring stream
profile `‖D^k N_v(ringStreamProfile R Φ)‖ ≤ C √s (1+s)^{K+1} (1+|η|)^{k+1} ∑_{i ≤ k+1} ‖D^iΦ‖`
(`nvJetSqrt`).  With `(1+|y|)√s ≤ √s + R + |η|` (`geom_ring`) this gives the inverse-distance
weight on every bounded age range (`nvDecayFar`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.IterQuadInlet

open UnforcedLeray UnforcedLeray.Short.IIb

/-- `‖D^j N_v b(τ, y)‖ ≤ C √s (1+s)^k (1+|η|)^j ∑_{l ≤ j} ‖D^l b(chart R τ y)‖` off the axis,
uniformly in `R ≥ 1`, `τ`, `b`. -/
theorem ringLiftPtJetSqrt (j : ℕ) : ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (R τ : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid), 1 ≤ R → ContDiffOn ℝ ∞ b (Ioi 0 ×ˢ univ) →
      ∀ y : Space, y ∉ Axi.axis →
        ‖iteratedFDeriv ℝ j (Axi.Nv R b τ) y‖ ≤
          C * √(Axi.age R y) * (1 + Axi.age R y) ^ k * (1 + |Axi.trans R y|) ^ j *
            ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := by
  have hSFall : ∀ i : ℕ, ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ (S R : ℝ), 0 < S → 1 ≤ R →
      ∀ y : Space, y ∉ Axi.axis → Axi.age R y < S →
        ‖iteratedFDeriv ℝ i (fun z => √(Axi.age R z)) y‖ ≤ C * (1 + S) ^ k ∧
        ‖iteratedFDeriv ℝ i Axi.frameL y‖ ≤ C * (1 + S) ^ k :=
    fun i => sqrtFrameJets i
  choose Cs ks hCs hSF using hSFall
  choose Ci hCi hInv using fun i => SqrtFrameJetsAux.varrho_inv_jet i
  obtain ⟨C2, k2, hC2, hcc⟩ := PartIIIb.Concrete.compChartPtJet j
  obtain ⟨Cq, hCq⟩ : ∃ x : ℝ, x = ∑ i ∈ Finset.range (j + 1), Cs i := ⟨_, rfl⟩
  obtain ⟨Kq, hKq⟩ : ∃ K : ℕ, K = ∑ i ∈ Finset.range (j + 1), ks i := ⟨_, rfl⟩
  obtain ⟨Cv, hCv⟩ : ∃ x : ℝ, x = ∑ i ∈ Finset.range (j + 1), Ci i := ⟨_, rfl⟩
  have hCs_le : ∀ i, i ≤ j → Cs i ≤ Cq := fun i hi => by
    rw [hCq]
    exact Finset.single_le_sum (f := Cs) (fun l _ => (hCs l).le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hks_le : ∀ i, i ≤ j → ks i ≤ Kq := fun i hi => by
    rw [hKq]
    exact Finset.single_le_sum (f := ks) (fun l _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hCi_le : ∀ i, i ≤ j → Ci i ≤ Cv := fun i hi => by
    rw [hCv]
    exact Finset.single_le_sum (f := Ci) (fun l _ => (hCi l).le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  have hCq0 : 0 < Cq := by
    rw [hCq]
    exact Finset.sum_pos (fun l _ => hCs l) ⟨0, by simp⟩
  have hCv0 : 0 < Cv := by
    rw [hCv]
    exact Finset.sum_pos (fun l _ => hCi l) ⟨0, by simp⟩
  refine ⟨(((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cv * Cq * C2 * 2 ^ (j + Kq), j + Kq + k2,
    by positivity, ?_⟩
  intro R τ b hR hb y hy
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hR0 : R ≠ 0 := hRpos.ne'
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hmaps : MapsTo (Axi.chart R τ) Axi.axisᶜ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro z hz
    exact ⟨PartIIIb.Concrete.age_pos_of hRpos hz, mem_univ _⟩
  have hbc : ContDiffOn ℝ ∞ (fun z => b (Axi.chart R τ z)) Axi.axisᶜ :=
    hb.comp (ChartJetsAux.contDiffOn_chart hR0 τ) hmaps
  have hyc : y ∈ (Axi.axisᶜ : Set Space) := hy
  have hage : 0 < Axi.age R y := PartIIIb.Concrete.age_pos_of hRpos hy
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Axi.age R y + 1 := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; linarith
  have hageL : Axi.age R y < L := by rw [hL]; linarith
  have hpos : 0 ≤ 1 + L := by linarith
  have hS1 : (1 : ℝ) ≤ 1 + L := by linarith
  have hsub : 1 + L ≤ 2 * (1 + Axi.age R y) := by rw [hL]; linarith
  have hP0 : (0 : ℝ) ≤ 1 + Axi.age R y := by linarith
  have hT0 : (0 : ℝ) ≤ 1 + |Axi.trans R y| := by linarith [abs_nonneg (Axi.trans R y)]
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = √(Axi.age R y) := ⟨_, rfl⟩
  have hσ0 : 0 ≤ σ := by rw [hσ]; exact Real.sqrt_nonneg _
  obtain ⟨Bc, hBc⟩ : ∃ B : ℝ, B = C2 * (1 + Axi.age R y) ^ k2 * (1 + |Axi.trans R y|) ^ j *
      ∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖ := ⟨_, rfl⟩
  have hBc0 : 0 ≤ Bc := by
    rw [hBc]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC2.le (pow_nonneg hP0 _)) (pow_nonneg hT0 _))
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  -- the inverse radius `t = ϱ⁻¹` and `R t = √s`
  have hϱ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Axi.ϱ y)⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact inv_pos.2 hϱ
  have hRt : R * t = σ := by rw [hσ, Axi.sqrt_age hRpos hy, ht, div_eq_mul_inv]
  have htσ : t ≤ σ := by rw [← hRt]; nlinarith
  have hσL : σ ≤ 1 + L := by
    have hsq : σ ^ 2 = Axi.age R y := by rw [hσ]; exact Real.sq_sqrt hage.le
    rw [hL]
    nlinarith [sq_nonneg (σ - 1)]
  -- refined amplitude jets: `‖D^i √s‖ ≤ Cv √s (1+L)^j`
  have hA : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun z => √(Axi.age R z)) Axi.axisᶜ y‖
      ≤ Cv * σ * (1 + L) ^ j := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => √(Axi.age R z)) i hopen hyc]
    have hfun : (fun z : Space => √(Axi.age R z)) =ᶠ[𝓝 y]
        (R • fun z : Space => (Axi.ϱ z)⁻¹) := by
      filter_upwards [hopen.mem_nhds hyc] with z hz
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Axi.sqrt_age hRpos hz, div_eq_mul_inv]
    have hcd : ContDiffAt ℝ i (fun z : Space => (Axi.ϱ z)⁻¹) y :=
      ((Axi.contDiffOn_ϱ.inv fun _ hz => Axi.ϱ_ne_zero hz).contDiffAt
        (hopen.mem_nhds hyc)).of_le (by exact_mod_cast le_top)
    have hD : iteratedFDeriv ℝ i (fun z : Space => √(Axi.age R z)) y =
        R • iteratedFDeriv ℝ i (fun z : Space => (Axi.ϱ z)⁻¹) y := by
      rw [hfun.iteratedFDeriv ℝ i |>.self_of_nhds, iteratedFDeriv_const_smul_apply hcd]
    rw [hD, norm_smul, Real.norm_of_nonneg hRpos.le]
    have hI := hInv i y hy
    rw [← ht] at hI
    calc R * ‖iteratedFDeriv ℝ i (fun z : Space => (Axi.ϱ z)⁻¹) y‖
        ≤ R * (Ci i * t ^ (i + 1)) := mul_le_mul_of_nonneg_left hI hRpos.le
      _ = Ci i * (R * t) * t ^ i := by ring
      _ = Ci i * σ * t ^ i := by rw [hRt]
      _ ≤ Cv * σ * (1 + L) ^ j := by
        have h1 : t ^ i ≤ (1 + L) ^ j :=
          (pow_le_pow_left₀ ht0.le (htσ.trans hσL) i).trans (pow_le_pow_right₀ hS1 hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hCi_le i hi) hσ0) h1
          (pow_nonneg ht0.le _) (mul_nonneg hCv0.le hσ0)
  -- frame jets, order `≤ j`, at the level `L = age + 1`
  have hB : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i Axi.frameL Axi.axisᶜ y‖
      ≤ Cq * (1 + L) ^ Kq := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Axi.frameL) i hopen hyc]
    refine ((hSF i L R hL0 hR y hy hageL).2).trans ?_
    exact mul_le_mul (hCs_le i hi) (pow_le_pow_right₀ hS1 (hks_le i hi)) (pow_nonneg hpos _)
      hCq0.le
  -- composite jets, order `≤ j`
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (fun z => b (Axi.chart R τ z)) Axi.axisᶜ y‖
      ≤ Bc := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun z => b (Axi.chart R τ z)) i hopen hyc,
      hBc]
    exact hcc R τ b hR hb y hy i hi
  have hX : 0 ≤ Cq * (1 + L) ^ Kq := mul_nonneg hCq0.le (pow_nonneg hpos _)
  -- the frame times the composite
  have hGc : ∀ m, m ≤ j → ‖iteratedFDerivWithin ℝ m
      (fun z => Axi.frameL z (b (Axi.chart R τ z))) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + L) ^ Kq) * Bc := by
    intro m hm
    have h := RingLiftOffAxisAux.clm_bound (f := Axi.frameL) (g := fun z => b (Axi.chart R τ z))
      (n := m) (A := Cq * (1 + L) ^ Kq) (B := Bc)
      ChartJetsAux.contDiffOn_frameL hbc hopen.uniqueDiffOn hyc
      (fun i hi => hB i (hi.trans hm)) (fun i hi => hC i (hi.trans hm))
    refine h.trans ?_
    have hmono : ((m : ℝ) + 1) * 2 ^ m ≤ ((j : ℝ) + 1) * 2 ^ j := by
      have h1 : (m : ℝ) ≤ j := by exact_mod_cast hm
      have h2 : (2 : ℝ) ^ m ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hm
      exact mul_le_mul (by linarith) h2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hX) hBc0
  -- Leibniz for the amplitude times the frame-composite
  have hSmul : ‖iteratedFDerivWithin ℝ j (fun z => √(Axi.age R z) • Axi.frameL z
      (b (Axi.chart R τ z))) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cv * σ * (1 + L) ^ j) *
        (((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + L) ^ Kq) * Bc) :=
    RingLiftOffAxisAux.smul_bound (f := fun z => √(Axi.age R z))
      (g := fun z => Axi.frameL z (b (Axi.chart R τ z))) (n := j)
      (A := Cv * σ * (1 + L) ^ j)
      (B := ((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + L) ^ Kq) * Bc)
      (ChartJetsAux.contDiffOn_sqrt_age hR0)
      (ChartJetsAux.contDiffOn_frameL.clm_apply hbc)
      hopen.uniqueDiffOn hyc hA (fun i hi => hGc i hi)
  -- conversion to the global derivative
  have e := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Axi.Nv R b τ) j hopen hyc
  have hNv : ‖iteratedFDerivWithin ℝ j (Axi.Nv R b τ) Axi.axisᶜ y‖
      ≤ ((j : ℝ) + 1) * 2 ^ j * (Cv * σ * (1 + L) ^ j) *
        (((j : ℝ) + 1) * 2 ^ j * (Cq * (1 + L) ^ Kq) * Bc) := by
    rw [ChartJetsAux.Nv_eq_fun]
    exact hSmul
  rw [← e]
  refine hNv.trans ?_
  have hL2 : (1 + L) ^ j * (1 + L) ^ Kq ≤ 2 ^ (j + Kq) * (1 + Axi.age R y) ^ (j + Kq) := by
    calc (1 + L) ^ j * (1 + L) ^ Kq = (1 + L) ^ (j + Kq) := by rw [← pow_add]
      _ ≤ (2 * (1 + Axi.age R y)) ^ (j + Kq) := pow_le_pow_left₀ hpos hsub _
      _ = 2 ^ (j + Kq) * (1 + Axi.age R y) ^ (j + Kq) := mul_pow _ _ _
  rw [← hσ]
  calc _ = (((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cv * Cq * σ * ((1 + L) ^ j * (1 + L) ^ Kq) * Bc := by
        ring
    _ ≤ (((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cv * Cq * σ *
          (2 ^ (j + Kq) * (1 + Axi.age R y) ^ (j + Kq)) * Bc := by
        refine mul_le_mul_of_nonneg_right ?_ hBc0
        exact mul_le_mul_of_nonneg_left hL2 (by positivity)
    _ = ((((j : ℝ) + 1) * 2 ^ j) ^ 2 * Cv * Cq * C2 * 2 ^ (j + Kq)) * σ *
          (1 + Axi.age R y) ^ (j + Kq + k2) * (1 + |Axi.trans R y|) ^ j *
          (∑ l ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖) := by
        rw [hBc, pow_add (1 + Axi.age R y) (j + Kq) k2]
        ring

/-- **Stream form**: `‖D^k N_v(ringStreamProfile R Φ)(τ, y)‖ ≤
C √s (1+s)^{K+1} (1+|η|)^{k+1} ∑_{i ≤ k+1} ‖D^iΦ(chart R τ y)‖` off the axis, `R ≥ 1`. -/
theorem nvJetSqrt (k : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧
      ∀ (R : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ), 1 ≤ R → ContDiffOn ℝ ∞ Φ (Ioi 0 ×ˢ univ) →
        ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
          ‖iteratedFDeriv ℝ k (Axi.Nv R (Axi.ringStreamProfile R Φ) τ) y‖ ≤
            C * √(Axi.age R y) * (1 + Axi.age R y) ^ (K + 1) * ((1 + |Axi.trans R y|) ^ (k + 1) *
              ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖) := by
  obtain ⟨CJ, K, hCJ, HJ⟩ := ringLiftPtJetSqrt k
  choose CP hCP0 hCP using fun l => PartIIa.ringProfileMeridJet_unif l
  have hCP_sum : 0 ≤ ∑ l ∈ Finset.range (k + 1), CP l :=
    Finset.sum_nonneg fun l _ => hCP0 l
  refine ⟨CJ * ∑ l ∈ Finset.range (k + 1), CP l, K, mul_nonneg hCJ.le hCP_sum,
    fun R Φ hR hΦ τ y hy => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hs : 0 < Axi.age R y := PartIIIb.Concrete.age_pos_of hR0 hy
  have hBs : ContDiffOn ℝ ∞ (Axi.ringStreamProfile R Φ) (Ioi 0 ×ˢ univ) := (hCP 0 R Φ hR hΦ).1
  have h1 := HJ R τ _ hR hBs y hy
  have hfac : 1 + |(Axi.chart R τ y).1| + |(Axi.chart R τ y).2.2| ≤
      (1 + Axi.age R y) * (1 + |Axi.trans R y|) := by
    show 1 + |Axi.age R y| + |Axi.trans R y| ≤ (1 + Axi.age R y) * (1 + |Axi.trans R y|)
    rw [abs_of_pos hs]
    nlinarith [abs_nonneg (Axi.trans R y)]
  have h1s : 0 ≤ 1 + Axi.age R y := by linarith
  have hσ0 : 0 ≤ √(Axi.age R y) := Real.sqrt_nonneg _
  have hl : ∀ l ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R Φ) (Axi.chart R τ y)‖ ≤
        CP l * ((1 + Axi.age R y) * (1 + |Axi.trans R y|)) *
          ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ := by
    intro l hl
    have hl' : l + 2 ≤ k + 2 := by have := Finset.mem_range.1 hl; omega
    have h2 := (hCP l R Φ hR hΦ).2 (Axi.chart R τ y) hs
    have hsub : ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ ≤
        ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hl')
        (fun _ _ _ => norm_nonneg _)
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range (l + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine h2.trans (mul_le_mul ?_ hsub hsum0
      (mul_nonneg (hCP0 l) (mul_nonneg h1s (by positivity))))
    exact mul_le_mul_of_nonneg_left hfac (hCP0 l)
  have hsumB : ∑ l ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R Φ) (Axi.chart R τ y)‖ ≤
        (∑ l ∈ Finset.range (k + 1), CP l) * ((1 + Axi.age R y) * (1 + |Axi.trans R y|)) *
          ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum hl
  have hpos1 : 0 ≤ CJ * √(Axi.age R y) * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg hCJ.le hσ0) (pow_nonneg h1s _))
      (pow_nonneg (by positivity) _)
  calc ‖iteratedFDeriv ℝ k (Axi.Nv R (Axi.ringStreamProfile R Φ) τ) y‖
      ≤ CJ * √(Axi.age R y) * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ k *
          ∑ l ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ l (Axi.ringStreamProfile R Φ) (Axi.chart R τ y)‖ := h1
    _ ≤ CJ * √(Axi.age R y) * (1 + Axi.age R y) ^ K * (1 + |Axi.trans R y|) ^ k *
          ((∑ l ∈ Finset.range (k + 1), CP l) * ((1 + Axi.age R y) * (1 + |Axi.trans R y|)) *
            ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖) :=
        mul_le_mul_of_nonneg_left hsumB hpos1
    _ = CJ * (∑ l ∈ Finset.range (k + 1), CP l) * √(Axi.age R y) * (1 + Axi.age R y) ^ (K + 1) *
          ((1 + |Axi.trans R y|) ^ (k + 1) *
            ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖) := by
        ring

/-- **Inverse-distance weight on a bounded age range**: for `R ≥ 1`, `0 ≤ S` and `y` off the axis
with `s = age R y ≤ S`,
`(1+|y|) ‖D^k N_v(ringStreamProfile R Φ)(τ, y)‖ ≤ C (1+S+R)^{K+2} (1+|η|)^{k+2} ∑_{i ≤ k+1} ‖D^iΦ‖`. -/
theorem nvDecayFar (k : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧
      ∀ (R S : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ), 1 ≤ R → 0 ≤ S → ContDiffOn ℝ ∞ Φ (Ioi 0 ×ˢ univ) →
        ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis → Axi.age R y ≤ S →
          (1 + ‖y‖) * ‖iteratedFDeriv ℝ k (Axi.Nv R (Axi.ringStreamProfile R Φ) τ) y‖ ≤
            C * (1 + S + R) ^ (K + 2) * ((1 + |Axi.trans R y|) ^ (k + 2) *
              ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖) := by
  obtain ⟨C, K, hC0, H⟩ := nvJetSqrt k
  refine ⟨C, K, hC0, fun R S Φ hR hS hΦ τ y hy hsS => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hs : 0 < Axi.age R y := PartIIIb.Concrete.age_pos_of hR0 hy
  have h1 := H R Φ hR hΦ τ y hy
  obtain ⟨g1, -⟩ := PartIIIb.Concrete.geom_ring hR0 hy
  set σ := √(Axi.age R y) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσS : σ ≤ 1 + S := by
    have hsq : σ ^ 2 = Axi.age R y := Real.sq_sqrt hs.le
    nlinarith [sq_nonneg (σ - 1)]
  set η := |Axi.trans R y| with hη
  have hη0 : 0 ≤ η := abs_nonneg _
  set SS := ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i Φ (Axi.chart R τ y)‖ with hSS
  have hSS0 : 0 ≤ SS := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB : 1 ≤ 1 + S + R := by linarith
  have hy0 : 0 ≤ 1 + ‖y‖ := by positivity
  have hw : (1 + ‖y‖) * σ ≤ (1 + S + R) * (1 + η) := by
    refine g1.trans ?_
    nlinarith
  have hpow : (1 + Axi.age R y) ^ (K + 1) ≤ (1 + S + R) ^ (K + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  calc (1 + ‖y‖) * ‖iteratedFDeriv ℝ k (Axi.Nv R (Axi.ringStreamProfile R Φ) τ) y‖
      ≤ (1 + ‖y‖) * (C * σ * (1 + Axi.age R y) ^ (K + 1) * ((1 + η) ^ (k + 1) * SS)) :=
        mul_le_mul_of_nonneg_left h1 hy0
    _ = C * ((1 + ‖y‖) * σ) * (1 + Axi.age R y) ^ (K + 1) * ((1 + η) ^ (k + 1) * SS) := by ring
    _ ≤ C * ((1 + S + R) * (1 + η)) * (1 + S + R) ^ (K + 1) * ((1 + η) ^ (k + 1) * SS) := by
        gcongr
    _ = C * (1 + S + R) ^ (K + 2) * ((1 + η) ^ (k + 2) * SS) := by ring

end UnforcedLeray.Short.IIb.IterQuadInlet
