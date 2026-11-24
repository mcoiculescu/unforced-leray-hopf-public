import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_8

/-!
# Part II-b, task `PartII-b:G4/3/8/7` (`DiffReal` from its parts): the real column difference

Source of record: `the November 2 reference manuscript` (SP), lines 2375-2379.
On `0 < s ≤ H/2`, `colEpsR - flatReal = s[(dS e - dS e_0) - ν(vecDiffEps e - Δe_0) + (B_εe - B_0e_0)]`
with `e = e_0 + εe_1` (`inletSplit`). Each bracket term is `O(ε)` by the parts:
the chart derivative linearity, `JetLe`, `VecDiffFlat`, `VecDiffJet`, `BEpsFlat`, `RawProfJet`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete

/-! ## Calculus helpers -/

theorem dr_fderiv_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Coord → E} {c : ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (w : Coord) :
    fderiv ℝ (fun y => F y + c • G y) x w = fderiv ℝ F x w + c • fderiv ℝ G x w := by
  have e : (fun y => F y + c • G y) = F + c • G := rfl
  have e2 : fderiv ℝ (c • G) x = c • fderiv ℝ G x := fderiv_const_smul hG c
  rw [e, fderiv_add hF (hG.const_smul c), e2]
  simp

theorem dr_dQ_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Coord → E} {c : ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    Axi.dQ (fun y => F y + c • G y) x = Axi.dQ F x + c • Axi.dQ G x := by
  unfold Axi.dQ
  exact dr_fderiv_add_smul hF hG _

theorem dr_dEta_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Coord → E} {c : ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    Axi.dEta (fun y => F y + c • G y) x = Axi.dEta F x + c • Axi.dEta G x := by
  unfold Axi.dEta
  exact dr_fderiv_add_smul hF hG _

theorem dr_dS_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Coord → E} {c : ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    Axi.dS (fun y => F y + c • G y) x = Axi.dS F x + c • Axi.dS G x := by
  unfold Axi.dS
  exact dr_fderiv_add_smul hF hG _

theorem dr_kAge_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Coord → E} {c : ℝ} {x : Coord} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    kAge (fun y => F y + c • G y) x = kAge F x + c • kAge G x := by
  unfold kAge
  rw [dr_dS_add_smul hF hG, dr_dEta_add_smul hF hG]
  module

theorem dr_norm_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (w : E) (C B : ℝ) (ha : |a| ≤ C) (hw : ‖w‖ ≤ B) : ‖a • w‖ ≤ C * B := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul ha hw (norm_nonneg _) ((abs_nonneg _).trans ha)

theorem dr_norm_add_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u w : E) (ε A B : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hu : ‖u‖ ≤ A) (hw : ‖w‖ ≤ B) :
    ‖u + ε • w‖ ≤ A + B := by
  have hB : 0 ≤ B := (norm_nonneg w).trans hw
  have h1 : ‖ε • w‖ ≤ B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0]
    exact (mul_le_of_le_one_left (norm_nonneg w) hε1).trans hw
  exact (norm_add_le u (ε • w)).trans (add_le_add hu h1)

theorem dr_comp_le (w : Axi.Merid) (i : Fin 2) (C : ℝ) (h : ‖w‖ ≤ C) : |w i| ≤ C := by
  have := PiLp.norm_apply_le w i
  rw [Real.norm_eq_abs] at this
  exact this.trans h

theorem dr_chartJet_nonneg (G : Coord → Axi.Merid) (x : Coord) : 0 ≤ chartJet G x := by
  unfold chartJet
  positivity

theorem dr_cj_norm (G : Coord → Axi.Merid) (x : Coord) : ‖G x‖ ≤ chartJet G x := by
  unfold chartJet
  have := norm_nonneg (Axi.dQ G x)
  have := norm_nonneg (Axi.dEta G x)
  have := norm_nonneg (kAge G x)
  linarith

theorem dr_cj_dQ (G : Coord → Axi.Merid) (x : Coord) : ‖Axi.dQ G x‖ ≤ chartJet G x := by
  unfold chartJet
  have := norm_nonneg (G x)
  have := norm_nonneg (Axi.dEta G x)
  have := norm_nonneg (kAge G x)
  linarith

theorem dr_cj_dEta (G : Coord → Axi.Merid) (x : Coord) : ‖Axi.dEta G x‖ ≤ chartJet G x := by
  unfold chartJet
  have := norm_nonneg (G x)
  have := norm_nonneg (Axi.dQ G x)
  have := norm_nonneg (kAge G x)
  linarith

theorem dr_cj_kAge (G : Coord → Axi.Merid) (x : Coord) : ‖kAge G x‖ ≤ chartJet G x := by
  unfold chartJet
  have := norm_nonneg (G x)
  have := norm_nonneg (Axi.dQ G x)
  have := norm_nonneg (Axi.dEta G x)
  linarith

theorem dr_cj_sum (G : Coord → Axi.Merid) (x : Coord) : ‖kAge G x + G x‖ ≤ chartJet G x := by
  unfold chartJet
  have := norm_nonneg (Axi.dQ G x)
  have := norm_nonneg (Axi.dEta G x)
  linarith [norm_add_le (kAge G x) (G x)]

/-- The chart jet of `F + c • G` is at most the sum of the chart jets (`0 ≤ c ≤ 1`). -/
theorem dr_cj_add_smul_le (F G : Coord → Axi.Merid) {c : ℝ} {x : Coord}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    chartJet (fun y => F y + c • G y) x ≤ chartJet F x + chartJet G x := by
  unfold chartJet
  dsimp only
  rw [dr_dQ_add_smul hF hG, dr_dEta_add_smul hF hG, dr_kAge_add_smul hF hG]
  have h1 := dr_norm_add_smul_le (F x) (G x) c _ _ hc0 hc1 le_rfl le_rfl
  have h2 := dr_norm_add_smul_le (Axi.dQ F x) (Axi.dQ G x) c _ _ hc0 hc1 le_rfl le_rfl
  have h3 := dr_norm_add_smul_le (Axi.dEta F x) (Axi.dEta G x) c _ _ hc0 hc1 le_rfl le_rfl
  have h4 := dr_norm_add_smul_le (kAge F x) (kAge G x) c _ _ hc0 hc1 le_rfl le_rfl
  linarith

/-- Linearity of `flatB` in the profile. -/
theorem dr_flatB_add_smul (p : Params) (F G : Coord → Axi.Merid) {c : ℝ} {x : Coord}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    flatB p (fun y => F y + c • G y) x = flatB p F x + c • flatB p G x := by
  unfold flatB
  rw [dr_dQ_add_smul hF hG, dr_dEta_add_smul hF hG]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  module

/-- Size of `flatB p G x`: four products of a train jet and a jet of `G`. -/
theorem dr_flatB_norm_le (p : Params) (G : Coord → Axi.Merid) (x : Coord) :
    ‖flatB p G x‖ ≤ 4 * (chartJet (trainProf p) x * chartJet G x) := by
  unfold flatB
  have a1 : ‖trainProf p x 0 • Axi.dQ G x‖ ≤ chartJet (trainProf p) x * chartJet G x :=
    dr_norm_smul_le (trainProf p x 0) (Axi.dQ G x) (chartJet (trainProf p) x) (chartJet G x)
      (dr_comp_le (trainProf p x) 0 (chartJet (trainProf p) x) (dr_cj_norm (trainProf p) x))
      (dr_cj_dQ G x)
  have a2 : ‖trainProf p x 1 • Axi.dEta G x‖ ≤ chartJet (trainProf p) x * chartJet G x :=
    dr_norm_smul_le (trainProf p x 1) (Axi.dEta G x) (chartJet (trainProf p) x) (chartJet G x)
      (dr_comp_le (trainProf p x) 1 (chartJet (trainProf p) x) (dr_cj_norm (trainProf p) x))
      (dr_cj_dEta G x)
  have a3 : ‖G x 0 • Axi.dQ (trainProf p) x‖ ≤ chartJet G x * chartJet (trainProf p) x :=
    dr_norm_smul_le (G x 0) (Axi.dQ (trainProf p) x) (chartJet G x) (chartJet (trainProf p) x)
      (dr_comp_le (G x) 0 (chartJet G x) (dr_cj_norm G x)) (dr_cj_dQ (trainProf p) x)
  have a4 : ‖G x 1 • Axi.dEta (trainProf p) x‖ ≤ chartJet G x * chartJet (trainProf p) x :=
    dr_norm_smul_le (G x 1) (Axi.dEta (trainProf p) x) (chartJet G x) (chartJet (trainProf p) x)
      (dr_comp_le (G x) 1 (chartJet G x) (dr_cj_norm G x)) (dr_cj_dEta (trainProf p) x)
  have hsum : ∀ a b c d : Axi.Merid, ‖a + b + (c + d)‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    have e1 := norm_add_le (a + b) (c + d)
    have e2 := norm_add_le a b
    have e3 := norm_add_le c d
    linarith
  refine (hsum _ _ _ _).trans ?_
  have hc := mul_comm (chartJet G x) (chartJet (trainProf p) x)
  linarith

theorem dr_fderiv_apply_contDiff {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (v : Coord) :
    ContDiff ℝ ∞ (fun m => fderiv ℝ F m v) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem dr_dQ_contDiff {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Axi.dQ F) :=
  dr_fderiv_apply_contDiff hF _

theorem dr_dEta_contDiff {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Axi.dEta F) :=
  dr_fderiv_apply_contDiff hF _

theorem dr_dQdQ_add_smul {F G : Coord → Axi.Merid} {c : ℝ} {x : Coord}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    Axi.dQ (Axi.dQ (fun y => F y + c • G y)) x = Axi.dQ (Axi.dQ F) x + c • Axi.dQ (Axi.dQ G) x := by
  have h1 : Axi.dQ (fun y => F y + c • G y) = fun y => Axi.dQ F y + c • Axi.dQ G y := by
    funext y
    exact dr_dQ_add_smul (hF.differentiable (by simp) y) (hG.differentiable (by simp) y)
  rw [h1]
  exact dr_dQ_add_smul ((dr_dQ_contDiff hF).differentiable (by simp) x)
    ((dr_dQ_contDiff hG).differentiable (by simp) x)

theorem dr_dEtadEta_add_smul {F G : Coord → Axi.Merid} {c : ℝ} {x : Coord}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    Axi.dEta (Axi.dEta (fun y => F y + c • G y)) x =
      Axi.dEta (Axi.dEta F) x + c • Axi.dEta (Axi.dEta G) x := by
  have h1 : Axi.dEta (fun y => F y + c • G y) = fun y => Axi.dEta F y + c • Axi.dEta G y := by
    funext y
    exact dr_dEta_add_smul (hF.differentiable (by simp) y) (hG.differentiable (by simp) y)
  rw [h1]
  exact dr_dEta_add_smul ((dr_dEta_contDiff hF).differentiable (by simp) x)
    ((dr_dEta_contDiff hG).differentiable (by simp) x)

/-- Taylor-type bound for `iteratedFDeriv` of `F + c • G`. -/
theorem dr_iter_add_smul_le {F G : Coord → Axi.Merid} {c : ℝ} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (l : ℕ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x : Coord) :
    ‖iteratedFDeriv ℝ l (fun y => F y + c • G y) x‖ ≤
      ‖iteratedFDeriv ℝ l F x‖ + ‖iteratedFDeriv ℝ l G x‖ := by
  have hF' : ContDiffAt ℝ (l : WithTop ℕ∞) F x := (hF.of_le (by simp)).contDiffAt
  have hG' : ContDiffAt ℝ (l : WithTop ℕ∞) G x := (hG.of_le (by simp)).contDiffAt
  have hG'' : ContDiffAt ℝ (l : WithTop ℕ∞) (c • G) x := hG'.const_smul c
  have e : iteratedFDeriv ℝ l (fun y => F y + c • G y) x =
      iteratedFDeriv ℝ l F x + c • iteratedFDeriv ℝ l G x := by
    have h1 : (fun y => F y + c • G y) = F + c • G := rfl
    rw [h1, iteratedFDeriv_add_apply hF' hG'', iteratedFDeriv_const_smul_apply hG']
  rw [e]
  exact dr_norm_add_smul_le _ _ c _ _ hc0 hc1 le_rfl le_rfl

theorem dr_sum2 (F : Coord → Axi.Merid) (x : Coord) :
    ∑ l ∈ Finset.range 2, ‖iteratedFDeriv ℝ l F x‖ =
      ‖iteratedFDeriv ℝ 0 F x‖ + ‖iteratedFDeriv ℝ 1 F x‖ := by
  simp [Finset.sum_range_succ]

theorem dr_sum3 (F : Coord → Axi.Merid) (x : Coord) :
    ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l F x‖ =
      ‖iteratedFDeriv ℝ 0 F x‖ + ‖iteratedFDeriv ℝ 1 F x‖ + ‖iteratedFDeriv ℝ 2 F x‖ := by
  simp [Finset.sum_range_succ]

/-- Monotonicity of a monomial `c t^a L^b E` in the exponents (`t, L ≥ 1`, `E ≥ 0`, `c ≥ 0`). -/
theorem dr_mono (c t L E : ℝ) (a b a' b' : ℕ) (hc : 0 ≤ c) (ht : 1 ≤ t) (hL : 1 ≤ L)
    (hE : 0 ≤ E) (ha : a ≤ a') (hb : b ≤ b') : c * t ^ a * L ^ b * E ≤ c * t ^ a' * L ^ b' * E := by
  have h1 : t ^ a ≤ t ^ a' := pow_le_pow_right₀ ht ha
  have h2 : L ^ b ≤ L ^ b' := pow_le_pow_right₀ hL hb
  have h3 : 0 ≤ L ^ b := pow_nonneg (by linarith) _
  have h4 : 0 ≤ c * t ^ a' := mul_nonneg hc (pow_nonneg (by linarith) _)
  apply mul_le_mul_of_nonneg_right _ hE
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 h3 h4

/-- A jet bound of one inlet component from `JetLe` and `InletComponentJets`. -/
theorem dr_jet_bound (F : Coord → Axi.Merid) (x : Coord) (K M Q : ℝ) (hK : 0 ≤ K)
    (hM : 1 + |x.1| + |x.2.2| ≤ M) (hMn : 0 ≤ M) (hQ : 0 ≤ Q)
    (hJ : chartJet F x + ‖Axi.dS F x‖ ≤ K * (1 + |x.1| + |x.2.2|) *
      (‖iteratedFDeriv ℝ 0 F x‖ + ‖iteratedFDeriv ℝ 1 F x‖))
    (h0 : ‖iteratedFDeriv ℝ 0 F x‖ ≤ Q) (h1 : ‖iteratedFDeriv ℝ 1 F x‖ ≤ Q) :
    chartJet F x ≤ K * M * (2 * Q) ∧ ‖Axi.dS F x‖ ≤ K * M * (2 * Q) := by
  have hs : ‖iteratedFDeriv ℝ 0 F x‖ + ‖iteratedFDeriv ℝ 1 F x‖ ≤ 2 * Q := by linarith
  have hsn : 0 ≤ ‖iteratedFDeriv ℝ 0 F x‖ + ‖iteratedFDeriv ℝ 1 F x‖ := by positivity
  have hm : K * (1 + |x.1| + |x.2.2|) ≤ K * M := mul_le_mul_of_nonneg_left hM hK
  have hprod := mul_le_mul hm hs hsn (mul_nonneg hK hMn)
  have c0 := dr_chartJet_nonneg F x
  have c1 := norm_nonneg (Axi.dS F x)
  constructor <;> linarith

/-! ## The assembly -/

/-- **`DiffReal` from its parts** (SP 2375-2379). -/
theorem diffReal_of_parts (hT : TrainDiff) (hR : RawProfJet) (hC : InletComponentJets)
    (hF : VecDiffFlat) (hB : BEpsFlat) (hL : JetLe) (hV : VecDiffJet) : DiffReal := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨C, κ, k, N, ν₁, hC0, hκ, hν₁0, hν₁1, HC⟩ := hC Sig lam q hSig hq dm dp hdm 2
  obtain ⟨Cr, kr, Nr, νr, hCr, hνr0, hνr1, HR⟩ := hR Sig hSig dm dp hdm
  obtain ⟨K1, hK1, HF⟩ := hF
  obtain ⟨K2, hK2, HL⟩ := hL
  obtain ⟨K3, hK3, HV⟩ := hV
  have hS1 : 0 < 1 + Sig := by linarith
  refine ⟨2 * K2 * (1 + Sig) * C + 3 * (K1 + K3) * (1 + Sig) ^ 2 * C +
      56 * K2 * (1 + Sig) * C * Cr, κ, k + kr + 2, N + 2 + Nr, min ν₁ νr, ?_, hκ,
    lt_min hν₁0 hνr0, (min_le_left _ _).trans hν₁1, ?_⟩
  · have a1 := mul_pos (mul_pos hK2 hS1) hC0
    have a2 := mul_pos (mul_pos (add_pos hK1 hK3) (pow_pos hS1 2)) hC0
    have a3 := mul_pos (mul_pos (mul_pos hK2 hS1) hC0) hCr
    nlinarith
  intro p d hreg i x hs0 hsH
  obtain ⟨hBg, hνm, hS, hm⟩ := hreg
  have hν1' : p.ν ≤ ν₁ := hνm.trans (min_le_left _ _)
  have hνr' : p.ν ≤ νr := hνm.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν1'.trans hν₁1
  have hε0 : 0 ≤ p.ε := p.ε_pos.le
  have hεle : p.ε ≤ 1 := by
    rw [hBg.eps_eq, Real.exp_le_one_iff, neg_div]
    have hd : 0 < d := lt_of_lt_of_le hBg.dm_pos hBg.dm_le
    have : 0 ≤ d / p.ν := div_nonneg hd.le hνpos.le
    linarith
  have hreg1 : ColReg Sig q dm dp ν₁ p d := ⟨hBg, hν1', hS, hm⟩
  have hHeq : p.H = Sig * p.ν⁻¹ := by
    simp only [Params.H, hS, div_eq_mul_inv]
  have hHpos : 0 < p.H := p.H_pos
  have hxH : x.1 ≤ p.H := by linarith
  have hxH1 : x.1 ≤ Sig * p.ν⁻¹ := by linarith
  have hE_in : p.inletProfile i = fun y => inletE0 p i y + p.ε • inletE1 p i y :=
    inletSplit p i
  obtain ⟨hcd0, hcd1, HCb⟩ := HC p d hreg1 i
  have hd0 : DifferentiableAt ℝ (inletE0 p i) x := hcd0.differentiable (by simp) x
  have hd1 : DifferentiableAt ℝ (inletE1 p i) x := hcd1.differentiable (by simp) x
  obtain ⟨hTr, hRa⟩ := hT p d dm dp hBg x hs0
  obtain ⟨hJv, hJh, -⟩ := HR p d hBg hνr' hS x hs0 hxH
  -- the real parameters `t = 1/ν`, `L = 1+|η|`, `E = e^{-κ|η|/c}`
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = p.ν⁻¹ := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by rw [htdef]; exact (one_le_inv₀ hνpos).2 hν1
  have hpow : ∀ j : ℕ, (p.ν ^ j)⁻¹ = t ^ j := fun j => by rw [htdef, inv_pow]
  have hxH2 : x.1 ≤ Sig * t := by rw [htdef]; exact hxH1
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 1 + |x.2.2| := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith [abs_nonneg x.2.2]
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (-(κ * |x.2.2| / p.c)) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; exact (Real.exp_pos _).le
  have hMxL : 1 + |x.1| + |x.2.2| ≤ (1 + Sig) * t * L := by
    rw [abs_of_pos hs0, hLdef]
    have h1 : 0 ≤ |x.2.2| := abs_nonneg _
    have h2 : 0 ≤ (1 + Sig) * t - 1 := by nlinarith
    nlinarith [mul_nonneg h1 h2]
  have hYnn : 0 ≤ (1 + Sig) * t * L := by
    have h3 : 0 ≤ (1 + Sig) * t := mul_nonneg hS1.le (by linarith)
    exact mul_nonneg h3 (by linarith)
  have hQnn : 0 ≤ C * t ^ k * L ^ N * E :=
    mul_nonneg (mul_nonneg (mul_nonneg hC0.le (pow_nonneg (by linarith) k))
      (pow_nonneg (by linarith) N)) hE0
  -- the bound of the inlet components (from `InletComponentJets`)
  have hQ : ∀ l, l ≤ 2 → ‖iteratedFDeriv ℝ l (inletE0 p i) x‖ +
      ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ ≤ C * t ^ k * L ^ N * E := by
    intro l hl
    have h := HCb l hl x hxH
    rw [hpow k, ← hLdef, ← hEdef] at h
    exact h
  have hQ0 : ∀ l, l ≤ 2 → ‖iteratedFDeriv ℝ l (inletE0 p i) x‖ ≤ C * t ^ k * L ^ N * E :=
    fun l hl => by linarith [hQ l hl, norm_nonneg (iteratedFDeriv ℝ l (inletE1 p i) x)]
  have hQ1 : ∀ l, l ≤ 2 → ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ ≤ C * t ^ k * L ^ N * E :=
    fun l hl => by linarith [hQ l hl, norm_nonneg (iteratedFDeriv ℝ l (inletE0 p i) x)]
  have hQe : ∀ l, l ≤ 2 → ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
      C * t ^ k * L ^ N * E := by
    intro l hl
    rw [hE_in]
    exact (dr_iter_add_smul_le hcd0 hcd1 l hε0 hεle x).trans (hQ l hl)
  have hcdE : ContDiff ℝ ∞ (p.inletProfile i) := by
    rw [hE_in]
    exact hcd0.add (hcd1.const_smul p.ε)
  have hsumE : ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ ≤
      3 * (C * t ^ k * L ^ N * E) := by
    rw [dr_sum3]
    linarith [hQe 0 (by norm_num), hQe 1 (by norm_num), hQe 2 (by norm_num)]
  have hsumE1 : ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ ≤
      3 * (C * t ^ k * L ^ N * E) := by
    rw [dr_sum3]
    linarith [hQ1 0 (by norm_num), hQ1 1 (by norm_num), hQ1 2 (by norm_num)]
  -- the jets of the components (from `JetLe`)
  have hJL1 := HL (inletE1 p i) hcd1 x
  rw [dr_sum2] at hJL1
  have hJL0 := HL (inletE0 p i) hcd0 x
  rw [dr_sum2] at hJL0
  obtain ⟨hJ1, hdS1⟩ := dr_jet_bound (inletE1 p i) x K2 ((1 + Sig) * t * L)
    (C * t ^ k * L ^ N * E) hK2.le hMxL hYnn hQnn hJL1 (hQ1 0 (by norm_num))
    (hQ1 1 (by norm_num))
  obtain ⟨hJ0, -⟩ := dr_jet_bound (inletE0 p i) x K2 ((1 + Sig) * t * L)
    (C * t ^ k * L ^ N * E) hK2.le hMxL hYnn hQnn hJL0 (hQ0 0 (by norm_num))
    (hQ0 1 (by norm_num))
  -- chart identities at `x` for `e = e_0 + εe_1`
  have hdS : Axi.dS (p.inletProfile i) x =
      Axi.dS (inletE0 p i) x + p.ε • Axi.dS (inletE1 p i) x := by
    rw [hE_in]
    exact dr_dS_add_smul hd0 hd1
  have hflat : flatB p (p.inletProfile i) x =
      flatB p (inletE0 p i) x + p.ε • flatB p (inletE1 p i) x := by
    rw [hE_in]
    exact dr_flatB_add_smul p _ _ hd0 hd1
  have hJe : chartJet (p.inletProfile i) x ≤
      chartJet (inletE0 p i) x + chartJet (inletE1 p i) x := by
    rw [hE_in]
    exact dr_cj_add_smul_le _ _ hd0 hd1 hε0 hεle
  have hΔ : Axi.dQ (Axi.dQ (p.inletProfile i)) x + Axi.dEta (Axi.dEta (p.inletProfile i)) x =
      (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x) +
        p.ε • (Axi.dQ (Axi.dQ (inletE1 p i)) x + Axi.dEta (Axi.dEta (inletE1 p i)) x) := by
    rw [hE_in, dr_dQdQ_add_smul hcd0 hcd1, dr_dEtadEta_add_smul hcd0 hcd1]
    module
  -- the vector diffusion
  have hvF : ‖vecDiffEps p.ε (p.inletProfile i) x -
      (Axi.dQ (Axi.dQ (p.inletProfile i)) x + Axi.dEta (Axi.dEta (p.inletProfile i)) x)‖ ≤
      p.ε * K1 * ((1 + Sig) * t * L) ^ 2 * (3 * (C * t ^ k * L ^ N * E)) := by
    have h := HF p.ε hε0 hεle (p.inletProfile i) hcdE x
    have hsq : (1 + |x.1| + |x.2.2|) ^ 2 ≤ ((1 + Sig) * t * L) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMxL 2
    calc _ ≤ p.ε * K1 * (1 + |x.1| + |x.2.2|) ^ 2 *
          ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (p.inletProfile i) x‖ := h
      _ ≤ p.ε * K1 * ((1 + Sig) * t * L) ^ 2 * (3 * (C * t ^ k * L ^ N * E)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq (mul_nonneg hε0 hK1.le)) hsumE
            (Finset.sum_nonneg (fun l _ => norm_nonneg _))
            (mul_nonneg (mul_nonneg hε0 hK1.le) (sq_nonneg _))
  have hvV : ‖vecDiffEps 0 (inletE1 p i) x‖ ≤
      K3 * ((1 + Sig) * t * L) ^ 2 * (3 * (C * t ^ k * L ^ N * E)) := by
    have h := HV 0 le_rfl zero_le_one (inletE1 p i) hcd1 x
    have hsq : (1 + |x.1| + |x.2.2|) ^ 2 ≤ ((1 + Sig) * t * L) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hMxL 2
    calc _ ≤ K3 * (1 + |x.1| + |x.2.2|) ^ 2 *
          ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (inletE1 p i) x‖ := h
      _ ≤ K3 * ((1 + Sig) * t * L) ^ 2 * (3 * (C * t ^ k * L ^ N * E)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq hK3.le) hsumE1
            (Finset.sum_nonneg (fun l _ => norm_nonneg _))
            (mul_nonneg hK3.le (sq_nonneg _))
  have hVsplit : vecDiffEps p.ε (p.inletProfile i) x -
      (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x) =
      (vecDiffEps p.ε (p.inletProfile i) x -
        (Axi.dQ (Axi.dQ (p.inletProfile i)) x + Axi.dEta (Axi.dEta (p.inletProfile i)) x)) +
        p.ε • vecDiffEps 0 (inletE1 p i) x := by
    have hz : vecDiffEps 0 (inletE1 p i) x =
        Axi.dQ (Axi.dQ (inletE1 p i)) x + Axi.dEta (Axi.dEta (inletE1 p i)) x := by
      simp [vecDiffEps]
    rw [hz, hΔ]
    module
  have hVbd : ‖vecDiffEps p.ε (p.inletProfile i) x -
      (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x)‖ ≤
      p.ε * K1 * ((1 + Sig) * t * L) ^ 2 * (3 * (C * t ^ k * L ^ N * E)) +
        p.ε * (K3 * ((1 + Sig) * t * L) ^ 2 * (3 * (C * t ^ k * L ^ N * E))) := by
    rw [hVsplit]
    refine (norm_add_le _ _).trans (add_le_add hvF ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0]
    exact mul_le_mul_of_nonneg_left hvV hε0
  -- the interaction
  have hBsplit : bEps p (p.inletProfile i) x - flatB p (inletE0 p i) x =
      (bEps p (p.inletProfile i) x - flatB p (p.inletProfile i) x) +
        p.ε • flatB p (inletE1 p i) x := by
    rw [hflat]
    module
  have hJv' : chartJet (trainProf p) x ≤ Cr * t ^ kr * L ^ Nr := by
    rw [hpow kr, ← hLdef] at hJv
    exact hJv
  have hJh' : chartJet (raisedMerid p) x ≤ Cr * t ^ kr * L ^ Nr := by
    rw [hpow kr, ← hLdef] at hJh
    exact hJh
  have hVt : 0 ≤ Cr * t ^ kr * L ^ Nr :=
    mul_nonneg (mul_nonneg hCr.le (pow_nonneg (by linarith) kr)) (pow_nonneg (by linarith) Nr)
  have hX0 : 0 ≤ K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E)) :=
    mul_nonneg (mul_nonneg hK2.le hYnn) (mul_nonneg (by norm_num) hQnn)
  have hbE := hB p hε0 hεle (p.inletProfile i) x hTr hRa
  have hJe2 : chartJet (p.inletProfile i) x ≤
      2 * (K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E))) := by
    linarith [hJe, hJ0, hJ1]
  have hJvh : chartJet (trainProf p) x + chartJet (raisedMerid p) x ≤
      2 * (Cr * t ^ kr * L ^ Nr) := by
    linarith [hJv', hJh']
  have h6ε : 0 ≤ 6 * p.ε := by linarith
  have hε6 : 0 ≤ 6 * p.ε * (2 * (K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E)))) :=
    mul_nonneg h6ε (mul_nonneg (by norm_num) hX0)
  have hbA : ‖bEps p (p.inletProfile i) x - flatB p (p.inletProfile i) x‖ ≤
      6 * p.ε * (2 * (K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E)))) *
        (2 * (Cr * t ^ kr * L ^ Nr)) := by
    refine hbE.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hJe2 h6ε) hJvh
      (add_nonneg (dr_chartJet_nonneg _ _) (dr_chartJet_nonneg _ _)) hε6
  have hbB : ‖p.ε • flatB p (inletE1 p i) x‖ ≤
      p.ε * (4 * ((Cr * t ^ kr * L ^ Nr) * (K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E))))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0]
    refine mul_le_mul_of_nonneg_left ?_ hε0
    have h1 := dr_flatB_norm_le p (inletE1 p i) x
    have h2 : chartJet (trainProf p) x * chartJet (inletE1 p i) x ≤
        (Cr * t ^ kr * L ^ Nr) * (K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E))) :=
      mul_le_mul hJv' hJ1 (dr_chartJet_nonneg _ _) hVt
    linarith
  have hbnd : ‖bEps p (p.inletProfile i) x - flatB p (inletE0 p i) x‖ ≤
      p.ε * (28 * ((K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E))) *
        (Cr * t ^ kr * L ^ Nr))) := by
    rw [hBsplit]
    refine (norm_add_le _ _).trans ?_
    linarith [hbA, hbB]
  -- the derivative part
  have hdSpart : ‖Axi.dS (p.inletProfile i) x - Axi.dS (inletE0 p i) x‖ ≤
      p.ε * (K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E))) := by
    rw [hdS, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0]
    exact mul_le_mul_of_nonneg_left hdS1 hε0
  -- the algebraic identity `colEpsR - flatReal = s • B_k`
  have key : colEpsR p i x - flatReal p i x = x.1 •
      ((Axi.dS (p.inletProfile i) x - Axi.dS (inletE0 p i) x) -
        p.ν • (vecDiffEps p.ε (p.inletProfile i) x -
          (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x)) +
        (bEps p (p.inletProfile i) x - flatB p (inletE0 p i) x)) := by
    unfold colEpsR colDiffR colIntR flatReal
    rw [if_pos hs0]
    module
  have hνV : ‖p.ν • (vecDiffEps p.ε (p.inletProfile i) x -
      (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x))‖ ≤
      p.ε * K1 * ((1 + Sig) * t * L) ^ 2 * (3 * (C * t ^ k * L ^ N * E)) +
        p.ε * (K3 * ((1 + Sig) * t * L) ^ 2 * (3 * (C * t ^ k * L ^ N * E))) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hνpos]
    exact (mul_le_of_le_one_left (norm_nonneg _) hν1).trans hVbd
  have hBkb : ‖(Axi.dS (p.inletProfile i) x - Axi.dS (inletE0 p i) x) -
        p.ν • (vecDiffEps p.ε (p.inletProfile i) x -
          (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x)) +
        (bEps p (p.inletProfile i) x - flatB p (inletE0 p i) x)‖ ≤
      p.ε * (K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E))) +
        (p.ε * K1 * ((1 + Sig) * t * L) ^ 2 * (3 * (C * t ^ k * L ^ N * E)) +
          p.ε * (K3 * ((1 + Sig) * t * L) ^ 2 * (3 * (C * t ^ k * L ^ N * E)))) +
        p.ε * (28 * ((K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E))) *
          (Cr * t ^ kr * L ^ Nr))) := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add hdSpart hνV)) hbnd)
  -- the polynomial bookkeeping: each term is a monomial in `t`, `L`, `E` with exponents `≤` the final ones
  have hpoly : K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E)) +
      3 * (K1 + K3) * ((1 + Sig) * t * L) ^ 2 * (C * t ^ k * L ^ N * E) +
      28 * ((K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E))) *
        (Cr * t ^ kr * L ^ Nr)) ≤
      (2 * K2 * (1 + Sig) * C + 3 * (K1 + K3) * (1 + Sig) ^ 2 * C +
        56 * K2 * (1 + Sig) * C * Cr) * t ^ (k + kr + 2) * L ^ (N + 2 + Nr) * E := by
    have eX0 : K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E)) =
        (2 * K2 * (1 + Sig) * C) * t ^ (k + 1) * L ^ (N + 1) * E := by ring
    have eQ3 : 3 * (K1 + K3) * ((1 + Sig) * t * L) ^ 2 * (C * t ^ k * L ^ N * E) =
        (3 * (K1 + K3) * (1 + Sig) ^ 2 * C) * t ^ (k + 2) * L ^ (N + 2) * E := by ring
    have eV : 28 * ((K2 * ((1 + Sig) * t * L) * (2 * (C * t ^ k * L ^ N * E))) *
        (Cr * t ^ kr * L ^ Nr)) =
        (56 * K2 * (1 + Sig) * C * Cr) * t ^ (k + kr + 1) * L ^ (N + 1 + Nr) * E := by ring
    have hsum_eq : (2 * K2 * (1 + Sig) * C + 3 * (K1 + K3) * (1 + Sig) ^ 2 * C +
        56 * K2 * (1 + Sig) * C * Cr) * t ^ (k + kr + 2) * L ^ (N + 2 + Nr) * E =
        (2 * K2 * (1 + Sig) * C) * t ^ (k + kr + 2) * L ^ (N + 2 + Nr) * E +
        (3 * (K1 + K3) * (1 + Sig) ^ 2 * C) * t ^ (k + kr + 2) * L ^ (N + 2 + Nr) * E +
        (56 * K2 * (1 + Sig) * C * Cr) * t ^ (k + kr + 2) * L ^ (N + 2 + Nr) * E := by ring
    have m1 := dr_mono (2 * K2 * (1 + Sig) * C) t L E (k + 1) (N + 1) (k + kr + 2) (N + 2 + Nr)
      (by positivity) ht1 hL1 hE0 (by omega) (by omega)
    have m2 := dr_mono (3 * (K1 + K3) * (1 + Sig) ^ 2 * C) t L E (k + 2) (N + 2) (k + kr + 2)
      (N + 2 + Nr) (by positivity) ht1 hL1 hE0 (by omega) (by omega)
    have m3 := dr_mono (56 * K2 * (1 + Sig) * C * Cr) t L E (k + kr + 1) (N + 1 + Nr) (k + kr + 2)
      (N + 2 + Nr) (by positivity) ht1 hL1 hE0 (by omega) (by omega)
    rw [hsum_eq, eV, eX0, eQ3]
    linarith [m1, m2, m3]
  have hBk_final : ‖(Axi.dS (p.inletProfile i) x - Axi.dS (inletE0 p i) x) -
        p.ν • (vecDiffEps p.ε (p.inletProfile i) x -
          (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x)) +
        (bEps p (p.inletProfile i) x - flatB p (inletE0 p i) x)‖ ≤
      p.ε * ((2 * K2 * (1 + Sig) * C + 3 * (K1 + K3) * (1 + Sig) ^ 2 * C +
        56 * K2 * (1 + Sig) * C * Cr) * t ^ (k + kr + 2) * L ^ (N + 2 + Nr) * E) := by
    have hpe := mul_le_mul_of_nonneg_left hpoly hε0
    linarith [hBkb, hpe]
  -- conclusion
  rw [key, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hpow (k + kr + 2), ← hLdef, ← hEdef]
  calc x.1 * ‖(Axi.dS (p.inletProfile i) x - Axi.dS (inletE0 p i) x) -
        p.ν • (vecDiffEps p.ε (p.inletProfile i) x -
          (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x)) +
        (bEps p (p.inletProfile i) x - flatB p (inletE0 p i) x)‖
      ≤ x.1 * (p.ε * ((2 * K2 * (1 + Sig) * C + 3 * (K1 + K3) * (1 + Sig) ^ 2 * C +
        56 * K2 * (1 + Sig) * C * Cr) * t ^ (k + kr + 2) * L ^ (N + 2 + Nr) * E)) :=
        mul_le_mul_of_nonneg_left hBk_final hs0.le
    _ = p.ε * (2 * K2 * (1 + Sig) * C + 3 * (K1 + K3) * (1 + Sig) ^ 2 * C +
        56 * K2 * (1 + Sig) * C * Cr) * t ^ (k + kr + 2) * x.1 * L ^ (N + 2 + Nr) * E := by ring


end UnforcedLeray.Short.IIb
