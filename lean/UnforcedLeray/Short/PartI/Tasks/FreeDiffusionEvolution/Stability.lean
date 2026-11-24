import UnforcedLeray.Short.PartI.Sub.C02
import UnforcedLeray.Cons.L2.CanonicalBranch.DysonStage

/-!
# Target `PartI:C02`, sub-lemma 3: `FreeDiffusionStability`

Source of record: `the November 2 reference manuscript`, lines 1031-1049
("the Dyson series give the corresponding strong limits"). This file proves the `Prop`
`FreeDiffusionStability` of `Short/PartI/Sub/C02.lean` with no extra hypothesis.

Method. On a fixed block `[s,t]` the coefficient `β` enters through `freeDiffusionFamily β`
and the bounded interaction `transportDysonPert (-2iΩ) λ κ β`. A free evolution `F` with
`IsFreeDiffusionEvolution` is the Dyson sum of this pair (`dyson_unique`, `hasSum_dyson`).
Each Dyson term converges when `β_k → β` almost everywhere, by induction on the order `m`
(dominated convergence in the time integral, with the strong continuity of `a ↦ e^{aD}x`).
The series converges by `tendsto_tsum_of_dominated_convergence` with the majorant
`(C(t-s))^m / m! * ‖x‖`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Nat Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-! ### Elementary bounds and measurability -/

theorem fdsAbs_le {c βs : ℝ} (h : 0 ≤ c ∧ c ≤ βs) : |c| ≤ |βs| := by
  rw [abs_of_nonneg h.1]
  exact h.2.trans (le_abs_self βs)

theorem fdsIntervalIntegrable {β : ℝ → ℝ} {βs : ℝ} (hβm : Measurable β)
    (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs) (u v : ℝ) : IntervalIntegrable β volume u v := by
  refine (intervalIntegrable_const (c := |βs|)).mono_fun' hβm.aestronglyMeasurable ?_
  refine ae_of_all _ fun τ => ?_
  show ‖β τ‖ ≤ |βs|
  rw [Real.norm_eq_abs]
  exact fdsAbs_le (hβb τ)

/-! ### The free family and the interaction on a block -/

/-- The bounded transport `T = -2iΩ` (source line 967). -/
def fdsT : B0010.XG →L[ℂ] B0010.XG := (-2 * Complex.I) • B0012.omegaOp

/-- The free family on the block: `U(v,u) = e^{D ∫_u^v β}`. -/
def fdsFam (s t βs : ℝ) (β : ℝ → ℝ) (hβm : Measurable β)
    (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs) : UnforcedLeray.Evolution.EvolutionFamily B0010.XG s t :=
  UnforcedLeray.Cons.G3b.freeDiffusionFamily β (fun u v => fdsIntervalIntegrable hβm hβb u v)
    (fun τ => (hβb τ).1) |βs| (fun τ => fdsAbs_le (hβb τ))

/-- The bounded interaction `T - λ - β κ` on the block. -/
def fdsA (lam kappa : ℂ) (s t βs : ℝ) (β : ℝ → ℝ) (hβm : Measurable β)
    (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs) : UnforcedLeray.Evolution.BoundedPert B0010.XG s t :=
  UnforcedLeray.Cons.G3b.transportDysonPert fdsT lam kappa β s t
    hβm.aestronglyMeasurable.restrict ⟨|βs|, fun τ _ => fdsAbs_le (hβb τ)⟩

/-- The scalar coefficient `T - λ - z κ`. -/
def fdsPsi (T : B0010.XG →L[ℂ] B0010.XG) (lam kappa : ℂ) (z : ℂ) :
    B0010.XG →L[ℂ] B0010.XG :=
  T - lam • (1 : B0010.XG →L[ℂ] B0010.XG) - (z * kappa) • (1 : B0010.XG →L[ℂ] B0010.XG)

theorem fdsA_apply (lam kappa : ℂ) (s t βs : ℝ) (β : ℝ → ℝ) (hβm : Measurable β)
    (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs) (r : ℝ) :
    (fdsA lam kappa s t βs β hβm hβb).A r = fdsPsi fdsT lam kappa (β r : ℂ) := rfl

theorem fdsPsi_continuous (T : B0010.XG →L[ℂ] B0010.XG) (lam kappa : ℂ) (v : B0010.XG) :
    Continuous (fun z : ℂ => fdsPsi T lam kappa z v) := by
  have hψ : Continuous (fun z : ℂ => fdsPsi T lam kappa z) := by
    unfold fdsPsi
    fun_prop
  exact hψ.clm_apply continuous_const

/-- The uniform bound of the interaction on every block. -/
def fdsC (T : B0010.XG →L[ℂ] B0010.XG) (lam kappa : ℂ) (βs : ℝ) : ℝ :=
  ‖T‖ + ‖lam‖ * ‖(1 : B0010.XG →L[ℂ] B0010.XG)‖ +
    βs * ‖kappa‖ * ‖(1 : B0010.XG →L[ℂ] B0010.XG)‖

theorem fdsC_nonneg (T : B0010.XG →L[ℂ] B0010.XG) (lam kappa : ℂ) {βs : ℝ} (hβs : 0 ≤ βs) :
    0 ≤ fdsC T lam kappa βs := by
  unfold fdsC
  exact add_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (mul_nonneg (mul_nonneg hβs (norm_nonneg _)) (norm_nonneg _))

theorem fdsNorm_fdsPsi_le (T : B0010.XG →L[ℂ] B0010.XG) (lam kappa : ℂ) {βs z : ℝ}
    (hz : 0 ≤ z ∧ z ≤ βs) : ‖fdsPsi T lam kappa (z : ℂ)‖ ≤ fdsC T lam kappa βs := by
  have h1 := norm_sub_le (T - lam • (1 : B0010.XG →L[ℂ] B0010.XG))
    (((z : ℂ) * kappa) • (1 : B0010.XG →L[ℂ] B0010.XG))
  have h2 := norm_sub_le T (lam • (1 : B0010.XG →L[ℂ] B0010.XG))
  have h3 : ‖((z : ℂ) * kappa) • (1 : B0010.XG →L[ℂ] B0010.XG)‖ ≤
      βs * ‖kappa‖ * ‖(1 : B0010.XG →L[ℂ] B0010.XG)‖ := by
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hz.1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hz.2 (norm_nonneg _))
      (norm_nonneg _)
  have h4 : ‖lam • (1 : B0010.XG →L[ℂ] B0010.XG)‖ ≤
      ‖lam‖ * ‖(1 : B0010.XG →L[ℂ] B0010.XG)‖ := by
    rw [norm_smul]
  unfold fdsPsi fdsC
  linarith

theorem fdsA_norm_le (lam kappa : ℂ) (s t βs : ℝ) (β : ℝ → ℝ) (hβm : Measurable β)
    (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs) (r : ℝ) :
    ‖(fdsA lam kappa s t βs β hβm hβb).A r‖ ≤ fdsC fdsT lam kappa βs := by
  rw [fdsA_apply]
  exact fdsNorm_fdsPsi_le fdsT lam kappa (hβb r)

theorem fdsFam_norm_le (s t βs : ℝ) (β : ℝ → ℝ) (hβm : Measurable β)
    (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs) (u v : ℝ) :
    ‖(fdsFam s t βs β hβm hβb).U v u‖ ≤ 1 := by
  show ‖B0123.expD (∫ τ in u..v, β τ)‖ ≤ 1
  exact B0123.norm_expD_le _

/-! ### Uniform Dyson bounds on a block -/

/-- Dyson terms of a contraction family with interaction bounded by `C` obey the majorant
`(C(t-s))^m / m! ‖x‖`, uniformly for every endpoint in the block. -/
theorem fdsNorm_dysonTerm {s t : ℝ} (E : UnforcedLeray.Evolution.EvolutionFamily B0010.XG s t)
    (A : UnforcedLeray.Evolution.BoundedPert B0010.XG s t) {C : ℝ}
    (hE : ∀ u v, s ≤ u → u ≤ v → v ≤ t → ‖E.U v u‖ ≤ 1)
    (hA : ∀ r ∈ Icc s t, ‖A.A r‖ ≤ C) (m : ℕ) {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t)
    (x : B0010.XG) :
    ‖UnforcedLeray.Evolution.dysonTerm E A m u s x‖ ≤
      (C * (t - s)) ^ m / (m ! : ℝ) * ‖x‖ := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hA u ⟨hsu, hut⟩)
  have h := UnforcedLeray.Evolution.norm_dysonTerm_le_of_le E A
    (M := 1) (ω := 0) (C := C)
    (fun a b ha hab hb => by simpa using hE a b ha hab hb) hA m s u le_rfl hsu hut x
  have hmono : (C * (u - s)) ^ m / (m ! : ℝ) ≤ (C * (t - s)) ^ m / (m ! : ℝ) :=
    div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg hC (sub_nonneg.2 hsu))
        (mul_le_mul_of_nonneg_left (by linarith) hC) m)
      (by positivity)
  calc ‖UnforcedLeray.Evolution.dysonTerm E A m u s x‖
      ≤ 1 * Real.exp (0 * (u - s)) * ((1 * C * (u - s)) ^ m / (m ! : ℝ)) * ‖x‖ := h
    _ = (C * (u - s)) ^ m / (m ! : ℝ) * ‖x‖ := by simp
    _ ≤ (C * (t - s)) ^ m / (m ! : ℝ) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hmono (norm_nonneg _)

theorem fdsDysonBound (lam kappa : ℂ) (s t βs : ℝ) (β : ℝ → ℝ) (hβm : Measurable β)
    (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs) (m : ℕ) {u : ℝ} (hsu : s ≤ u) (hut : u ≤ t)
    (x : B0010.XG) :
    ‖UnforcedLeray.Evolution.dysonTerm (fdsFam s t βs β hβm hβb)
        (fdsA lam kappa s t βs β hβm hβb) m u s x‖ ≤
      (fdsC fdsT lam kappa βs * (t - s)) ^ m / (m ! : ℝ) * ‖x‖ :=
  fdsNorm_dysonTerm (fdsFam s t βs β hβm hβb) (fdsA lam kappa s t βs β hβm hβb)
    (fun a b _ _ _ => fdsFam_norm_le s t βs β hβm hβb a b)
    (fun r _ => fdsA_norm_le lam kappa s t βs β hβm hβb r) m hsu hut x

/-- One step of the Duhamel integrand is bounded by `C M` when the family has norm at most `1`,
the interaction has norm at most `C`, and the vector has norm at most `M`. -/
theorem fdsIntegrand_norm_le {s t : ℝ} (E : UnforcedLeray.Evolution.EvolutionFamily B0010.XG s t)
    (A : UnforcedLeray.Evolution.BoundedPert B0010.XG s t) {C M : ℝ} (hC : 0 ≤ C) (r u : ℝ)
    (hE : ‖E.U r u‖ ≤ 1) (hA : ‖A.A u‖ ≤ C) (z : B0010.XG) (hz : ‖z‖ ≤ M) :
    ‖E.U r u (A.A u z)‖ ≤ C * M := by
  have h1 : ‖A.A u z‖ ≤ C * M :=
    ((A.A u).le_opNorm z).trans (mul_le_mul hA hz (norm_nonneg z) hC)
  calc ‖E.U r u (A.A u z)‖ ≤ ‖E.U r u‖ * ‖A.A u z‖ := (E.U r u).le_opNorm _
    _ ≤ 1 * ‖A.A u z‖ := mul_le_mul_of_nonneg_right hE (norm_nonneg _)
    _ ≤ 1 * (C * M) := mul_le_mul_of_nonneg_left h1 zero_le_one
    _ = C * M := one_mul _

/-! ### Convergence of the coefficients and the free part -/

theorem fds_integral_tendsto {βs : ℝ} (βk : ℕ → ℝ → ℝ) (β : ℝ → ℝ)
    (hβkm : ∀ k, Measurable (βk k)) (hβkb : ∀ k τ, 0 ≤ βk k τ ∧ βk k τ ≤ βs)
    (hae : ∀ᵐ τ ∂(volume : Measure ℝ), Tendsto (fun k => βk k τ) atTop (𝓝 (β τ)))
    (u v : ℝ) :
    Tendsto (fun k => ∫ τ in u..v, βk k τ) atTop (𝓝 (∫ τ in u..v, β τ)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => |βs|) ?_ ?_ intervalIntegrable_const ?_
  · exact Eventually.of_forall fun k => (hβkm k).aestronglyMeasurable
  · refine Eventually.of_forall fun k => ae_of_all _ fun τ _ => ?_
    show ‖βk k τ‖ ≤ |βs|
    rw [Real.norm_eq_abs]
    exact fdsAbs_le (hβkb k τ)
  · filter_upwards [hae] with τ hτ _
    exact hτ

theorem fds_free_tendsto (s t βs : ℝ) (βk : ℕ → ℝ → ℝ) (β : ℝ → ℝ)
    (hβkm : ∀ k, Measurable (βk k)) (hβm : Measurable β)
    (hβkb : ∀ k τ, 0 ≤ βk k τ ∧ βk k τ ≤ βs) (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs)
    (hae : ∀ᵐ τ ∂(volume : Measure ℝ), Tendsto (fun k => βk k τ) atTop (𝓝 (β τ)))
    (u v : ℝ) (z : B0010.XG) :
    Tendsto (fun k => (fdsFam s t βs (βk k) (hβkm k) (hβkb k)).U v u z) atTop
      (𝓝 ((fdsFam s t βs β hβm hβb).U v u z)) := by
  have h := (UnforcedLeray.Cons.G3b.continuous_expD_apply z).tendsto (∫ τ in u..v, β τ)
  exact h.comp (fds_integral_tendsto βk β hβkm hβkb hae u v)

/-- Strong convergence of applied operators with a uniform norm bound. -/
theorem fds_tendsto_apply {ι : Type*} {l : Filter ι} {P : ι → B0010.XG →L[ℂ] B0010.XG}
    {Q : B0010.XG →L[ℂ] B0010.XG} {K : ℝ} (hK : ∀ i, ‖P i‖ ≤ K)
    (hP : ∀ v, Tendsto (fun i => P i v) l (𝓝 (Q v)))
    {z : ι → B0010.XG} {w : B0010.XG} (hz : Tendsto z l (𝓝 w)) :
    Tendsto (fun i => P i (z i)) l (𝓝 (Q w)) := by
  have hQ : Tendsto (fun i => ‖P i w - Q w‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hP w)
  have hz' : Tendsto (fun i => ‖z i - w‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hz
  have hbound : Tendsto (fun i => K * ‖z i - w‖ + ‖P i w - Q w‖) l (𝓝 0) := by
    have h := (hz'.const_mul K).add hQ
    rw [mul_zero, add_zero] at h
    exact h
  have key : ∀ i, ‖P i (z i) - Q w‖ ≤ K * ‖z i - w‖ + ‖P i w - Q w‖ := by
    intro i
    have e : P i (z i) - Q w = P i (z i - w) + (P i w - Q w) := by
      rw [map_sub]
      abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact ((P i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _))
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun i => norm_nonneg _) key hbound)

theorem fds_A_tendsto (lam kappa : ℂ) (s t βs : ℝ) (βk : ℕ → ℝ → ℝ) (β : ℝ → ℝ)
    (hβkm : ∀ k, Measurable (βk k)) (hβm : Measurable β)
    (hβkb : ∀ k τ, 0 ≤ βk k τ ∧ βk k τ ≤ βs) (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs)
    (u : ℝ) (hu : Tendsto (fun k => βk k u) atTop (𝓝 (β u))) (v : B0010.XG) :
    Tendsto (fun k => (fdsA lam kappa s t βs (βk k) (hβkm k) (hβkb k)).A u v) atTop
      (𝓝 ((fdsA lam kappa s t βs β hβm hβb).A u v)) := by
  have hc : Tendsto (fun k => ((βk k u : ℝ) : ℂ)) atTop (𝓝 ((β u : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hu
  simp only [fdsA_apply]
  exact ((fdsPsi_continuous fdsT lam kappa v).tendsto _).comp hc

/-! ### The Dyson sum of a free evolution -/

/-- A free evolution on the block `[s,t]` is the Dyson sum of the pair
(`freeDiffusionFamily β`, `transportDysonPert`). -/
theorem fds_hasSum (lam kappa : ℂ) (s t βs : ℝ) (β : ℝ → ℝ) (hβm : Measurable β)
    (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs) (F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG)
    (hF : IsFreeDiffusionEvolution lam kappa β F) (r : ℝ) (hsr : s ≤ r) (hrt : r ≤ t)
    (x : B0010.XG) :
    HasSum (fun m => UnforcedLeray.Evolution.dysonTerm (fdsFam s t βs β hβm hβb)
      (fdsA lam kappa s t βs β hβm hβb) m r s x) (F r s x) := by
  have hU : F r s = (UnforcedLeray.Evolution.dyson (fdsFam s t βs β hβm hβb)
      (fdsA lam kappa s t βs β hβm hβb)).U r s :=
    UnforcedLeray.Evolution.dyson_unique (fdsFam s t βs β hβm hβb)
      (fdsA lam kappa s t βs β hβm hβb) F
      (fun u _ _ y => (hF.cont y u).mono Icc_subset_Ici_self)
      (fun u v _ huv _ y => hF.duhamel u v huv y) s r le_rfl hsr hrt
  rw [hU]
  exact UnforcedLeray.Evolution.hasSum_dyson (fdsFam s t βs β hβm hβb)
    (fdsA lam kappa s t βs β hβm hβb) ⟨le_rfl, hsr, hrt⟩ x

/-! ### Convergence of every Dyson term -/

/-- Induction on the order `m`: every Dyson term converges, for every endpoint of the block. -/
theorem fds_P (lam kappa : ℂ) (s t βs : ℝ) (βk : ℕ → ℝ → ℝ) (β : ℝ → ℝ)
    (hβkm : ∀ k, Measurable (βk k)) (hβm : Measurable β)
    (hβkb : ∀ k τ, 0 ≤ βk k τ ∧ βk k τ ≤ βs) (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs)
    (hae : ∀ᵐ τ ∂(volume : Measure ℝ), Tendsto (fun k => βk k τ) atTop (𝓝 (β τ)))
    (x : B0010.XG) (m : ℕ) :
    ∀ r, s ≤ r → r ≤ t →
      Tendsto (fun k => UnforcedLeray.Evolution.dysonTerm
          (fdsFam s t βs (βk k) (hβkm k) (hβkb k))
          (fdsA lam kappa s t βs (βk k) (hβkm k) (hβkb k)) m r s x) atTop
        (𝓝 (UnforcedLeray.Evolution.dysonTerm
          (fdsFam s t βs β hβm hβb) (fdsA lam kappa s t βs β hβm hβb) m r s x)) := by
  induction m with
  | zero =>
    intro r hsr _
    simp only [UnforcedLeray.Evolution.dysonTerm_zero]
    exact fds_free_tendsto s t βs βk β hβkm hβm hβkb hβb hae s r x
  | succ m ih =>
    intro r hsr hrt
    have hβs0 : 0 ≤ βs := (hβb 0).1.trans (hβb 0).2
    have hC : 0 ≤ fdsC fdsT lam kappa βs := fdsC_nonneg fdsT lam kappa hβs0
    simp only [UnforcedLeray.Evolution.dysonTerm_succ]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (F := fun k u => (fdsFam s t βs (βk k) (hβkm k) (hβkb k)).U r u
          ((fdsA lam kappa s t βs (βk k) (hβkm k) (hβkb k)).A u
            (UnforcedLeray.Evolution.dysonTerm (fdsFam s t βs (βk k) (hβkm k) (hβkb k))
              (fdsA lam kappa s t βs (βk k) (hβkm k) (hβkb k)) m u s x)))
      (f := fun u => (fdsFam s t βs β hβm hβb).U r u
          ((fdsA lam kappa s t βs β hβm hβb).A u
            (UnforcedLeray.Evolution.dysonTerm (fdsFam s t βs β hβm hβb)
              (fdsA lam kappa s t βs β hβm hβb) m u s x)))
      (fun _ => fdsC fdsT lam kappa βs *
        ((fdsC fdsT lam kappa βs * (t - s)) ^ m / (m ! : ℝ) * ‖x‖))
      ?_ ?_ intervalIntegrable_const ?_
    · -- measurability of the Duhamel integrands
      refine Eventually.of_forall fun k => ?_
      rw [uIoc_of_le hsr]
      exact (fdsFam s t βs (βk k) (hβkm k) (hβkb k)).aestronglyMeasurable_integrand
        (fdsA lam kappa s t βs (βk k) (hβkm k) (hβkb k)) le_rfl hrt
        (((UnforcedLeray.Evolution.continuousOn_dysonTerm_fst
          (fdsFam s t βs (βk k) (hβkm k) (hβkb k))
          (fdsA lam kappa s t βs (βk k) (hβkm k) (hβkb k)) m x le_rfl).mono
          (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hrt))).aestronglyMeasurable
          measurableSet_Ioc)
    · -- domination, uniform in the index
      refine Eventually.of_forall fun k => ?_
      refine ae_of_all _ fun u hu => ?_
      rw [uIoc_of_le hsr] at hu
      exact fdsIntegrand_norm_le _ _ hC r u
        (fdsFam_norm_le s t βs (βk k) (hβkm k) (hβkb k) u r)
        (fdsA_norm_le lam kappa s t βs (βk k) (hβkm k) (hβkb k) u) _
        (fdsDysonBound lam kappa s t βs (βk k) (hβkm k) (hβkb k) m hu.1.le (hu.2.trans hrt) x)
    · -- almost everywhere convergence of the integrands
      filter_upwards [hae] with u hu hur
      rw [uIoc_of_le hsr] at hur
      have hsu : s ≤ u := hur.1.le
      have hut : u ≤ t := hur.2.trans hrt
      have hz1 := fds_tendsto_apply
        (P := fun k => (fdsA lam kappa s t βs (βk k) (hβkm k) (hβkb k)).A u)
        (Q := (fdsA lam kappa s t βs β hβm hβb).A u)
        (K := fdsC fdsT lam kappa βs)
        (fun k => fdsA_norm_le lam kappa s t βs (βk k) (hβkm k) (hβkb k) u)
        (fun v => fds_A_tendsto lam kappa s t βs βk β hβkm hβm hβkb hβb u hu v)
        (ih u hsu hut)
      exact fds_tendsto_apply
        (P := fun k => (fdsFam s t βs (βk k) (hβkm k) (hβkb k)).U r u)
        (Q := (fdsFam s t βs β hβm hβb).U r u)
        (K := 1)
        (fun k => fdsFam_norm_le s t βs (βk k) (hβkm k) (hβkb k) u r)
        (fun v => fds_free_tendsto s t βs βk β hβkm hβm hβkb hβb hae u r v) hz1

/-- The Dyson series converges: dominated convergence for series with the majorant
`(C(t-s))^m / m! ‖x‖`. -/
theorem fds_sum_tendsto (lam kappa : ℂ) (s t βs : ℝ) (hst : s ≤ t) (βk : ℕ → ℝ → ℝ)
    (β : ℝ → ℝ) (hβkm : ∀ k, Measurable (βk k)) (hβm : Measurable β)
    (hβkb : ∀ k τ, 0 ≤ βk k τ ∧ βk k τ ≤ βs) (hβb : ∀ τ, 0 ≤ β τ ∧ β τ ≤ βs)
    (hae : ∀ᵐ τ ∂(volume : Measure ℝ), Tendsto (fun k => βk k τ) atTop (𝓝 (β τ)))
    (x : B0010.XG) :
    Tendsto (fun k => ∑' m, UnforcedLeray.Evolution.dysonTerm
        (fdsFam s t βs (βk k) (hβkm k) (hβkb k))
        (fdsA lam kappa s t βs (βk k) (hβkm k) (hβkb k)) m t s x) atTop
      (𝓝 (∑' m, UnforcedLeray.Evolution.dysonTerm
        (fdsFam s t βs β hβm hβb) (fdsA lam kappa s t βs β hβm hβb) m t s x)) := by
  have hsum : Summable (fun m : ℕ =>
      (fdsC fdsT lam kappa βs * (t - s)) ^ m / (m ! : ℝ) * ‖x‖) :=
    (UnforcedLeray.Evolution.hasSum_pow_div_factorial
      (fdsC fdsT lam kappa βs * (t - s))).summable.mul_right ‖x‖
  refine tendsto_tsum_of_dominated_convergence hsum
    (fun m => fds_P lam kappa s t βs βk β hβkm hβm hβkb hβb hae x m t hst le_rfl) ?_
  refine Eventually.of_forall fun k m => ?_
  exact fdsDysonBound lam kappa s t βs (βk k) (hβkm k) (hβkb k) m hst le_rfl x

/-! ### The target -/

/-- **Sub-lemma 3 (stability under almost-everywhere convergence of `β`)**, source lines
1031-1049: the free evolutions `F_k` for `β_k` converge strongly to the free evolution `F` for
`β`, for every `s ≤ t` and `x`. -/
theorem freeDiffusionStability : FreeDiffusionStability := by
  unfold FreeDiffusionStability
  intro lam kappa βs βk β Fk F hβkm hβm hβkb hβb hae hFk hF s t hst x
  have h1 : ∀ k, ∑' m, UnforcedLeray.Evolution.dysonTerm
      (fdsFam s t βs (βk k) (hβkm k) (hβkb k))
      (fdsA lam kappa s t βs (βk k) (hβkm k) (hβkb k)) m t s x = Fk k t s x := fun k =>
    (fds_hasSum lam kappa s t βs (βk k) (hβkm k) (hβkb k) (Fk k) (hFk k) t hst le_rfl x).tsum_eq
  have h2 : ∑' m, UnforcedLeray.Evolution.dysonTerm
      (fdsFam s t βs β hβm hβb) (fdsA lam kappa s t βs β hβm hβb) m t s x = F t s x :=
    (fds_hasSum lam kappa s t βs β hβm hβb F hF t hst le_rfl x).tsum_eq
  rw [← h2]
  exact Tendsto.congr h1 (fds_sum_tendsto lam kappa s t βs hst βk β hβkm hβm hβkb hβb hae x)

end UnforcedLeray.Short.PartI
