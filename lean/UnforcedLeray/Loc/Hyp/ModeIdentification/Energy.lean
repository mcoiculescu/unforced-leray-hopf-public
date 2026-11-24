import UnforcedLeray.Loc.Hyp.ModeIdentification.Evolution

/-!
# H-ModeId helpers: the energy estimate and forward uniqueness

Support for `Loc/Hyp/ModeIdentification.lean` (target `ModeIdentificationHyp`,
`paper/main.tex` lines 313–316, blueprint unit B1010: "The linear energy estimate gives
uniqueness").

* `HasWeakLaplacian F L`: `L ∈ L²` is the Laplacian of `F ∈ H¹` in the `H¹` weak sense,
  `⟨L, G⟩ = -∑ᵢ ⟨∂ᵢF, ∂ᵢG⟩` for every `G ∈ H¹`; `H²` fields have it (`hasWeakLaplacian_h2`).
* `inner_le_energy`: for `δ ∈ X` with weak Laplacian `L` and `‖𝓑‖_{X→L²} ≤ M`,
  `⟨hL + 𝓑δ - σδ, δ⟩ ≤ (M + M²/(4h) + |σ|)‖δ‖₂²`. The manuscript bounds the coupling by
  `C‖∇U_*‖₃‖f‖₂‖∇f‖₂`; only the operator bound `𝓑_* ∈ L(X, L²_div)` of
  `loc:eq:coefficient-maps` (tex line 284) is used here, with Young's inequality against the
  dissipation `h‖∇δ‖₂²`.
* `energy_decay`: a Hilbert-valued path with a weak time derivative and
  `⟨u', u⟩ ≤ K‖u‖²` a.e. satisfies `‖ũ(t)‖² ≤ e^{2K(t-a)}‖ũ(a)‖²` (the weighted energy
  identity `BochnerTime.HasWeakDerivTime.weighted_norm_sq_sub` with weight `e^{-2Kr}`; this
  replaces Gronwall).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Blueprint.ModeId

open SobolevGraph
open UnforcedLeray.BochnerTime

/-! ## Weak time derivatives -/

section Time

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hasWeakDerivTime_mono {a b a' b' : ℝ} {u u' : ℝ → E} (h : HasWeakDerivTime a b u u')
    (ha : a ≤ a') (hb : b' ≤ b) : HasWeakDerivTime a' b' u u' :=
  ⟨h.int.mono_set (Ioo_subset_Ioo ha hb), h.int'.mono_set (Ioo_subset_Ioo ha hb),
    fun φ hφ hφs hφt => h.identity φ hφ hφs (hφt.trans (Ioo_subset_Ioo ha hb))⟩

/-- A path continuous on `[a,c]`, differentiable on `(a,c)` with a derivative continuous on
`[a,c]`, has that derivative as weak time derivative. -/
theorem hasWeakDerivTime_of_hasDerivAt {a c : ℝ} {u u' : ℝ → E} (hu : ContinuousOn u (Icc a c))
    (hd : ∀ t ∈ Ioo a c, HasDerivAt u (u' t) t) (hu' : ContinuousOn u' (Icc a c)) :
    HasWeakDerivTime a c u u' := by
  have hint : IntegrableOn u' (Ioo a c) := hu'.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine (hasWeakDerivTime_of_primitive hint (u a)).congr_ae ?_ (ae_eq_refl _)
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall (fun t ht => ?_)
  have hsub : Icc a t ⊆ Icc a c := Icc_subset_Icc_right ht.2.le
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1.le (hu.mono hsub)
    (fun s hs => hd s ⟨hs.1, hs.2.trans ht.2⟩) ((hu'.mono hsub).intervalIntegrable_of_Icc ht.1.le)
  rw [hftc]
  abel

end Time

section Energy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Energy decay** (B1010). If `⟨u', u⟩ ≤ K‖u‖²` almost everywhere on `(a,c)`, then the
continuous representative satisfies `‖ũ(t)‖² ≤ e^{2K(t-a)}‖ũ(a)‖²` on `[a,c]`. -/
theorem energy_decay {a c K : ℝ} {u u' : ℝ → H} (h : HasWeakDerivTime a c u u')
    (hK : ∀ᵐ r ∂(volume.restrict (Ioo a c)), inner ℝ (u' r) (u r) ≤ K * ‖u r‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc a c) :
    ‖h.rep t‖ ^ 2 ≤ Real.exp (2 * K * (t - a)) * ‖h.rep a‖ ^ 2 := by
  have hac : a ≤ c := ht.1.trans ht.2
  have ha : a ∈ Icc a c := ⟨le_rfl, hac⟩
  set w : ℝ → ℝ := fun r => Real.exp (-(2 * K) * r) with hwdef
  have hwd : ∀ r, HasDerivAt w (w r * (-(2 * K))) r := by
    intro r
    have := ((hasDerivAt_id r).const_mul (-(2 * K))).exp
    simpa [hwdef] using this
  have hw : ContDiff ℝ 1 w := by
    rw [hwdef]
    fun_prop
  have hid := h.weighted_norm_sq_sub hw ha ht
  have hle : ∫ r in a..t, (deriv w r * ‖h.rep r‖ ^ 2 + 2 * w r * inner ℝ (u' r) (h.rep r))
      ≤ 0 := by
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
    apply integral_nonpos_of_ae
    have h1 : ∀ᵐ r ∂(volume.restrict (Ioo a t)), inner ℝ (u' r) (u r) ≤ K * ‖u r‖ ^ 2 :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right ht.2) hK
    have h2 : ∀ᵐ r ∂(volume.restrict (Ioo a t)), u r = h.rep r :=
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right ht.2) h.ae_eq_rep
    filter_upwards [h1, h2] with r hr1 hr2
    rw [(hwd r).deriv, ← hr2]
    have hw0 : 0 < w r := Real.exp_pos _
    simp only [Pi.zero_apply]
    nlinarith
  have hwt : 0 < w t := Real.exp_pos _
  have hkey : w t * ‖h.rep t‖ ^ 2 ≤ w a * ‖h.rep a‖ ^ 2 := by linarith
  have hratio : w a = Real.exp (2 * K * (t - a)) * w t := by
    simp only [hwdef, ← Real.exp_add]
    ring_nf
  rw [hratio] at hkey
  have hkey' : w t * ‖h.rep t‖ ^ 2 ≤ w t * (Real.exp (2 * K * (t - a)) * ‖h.rep a‖ ^ 2) := by
    calc w t * ‖h.rep t‖ ^ 2 ≤ Real.exp (2 * K * (t - a)) * w t * ‖h.rep a‖ ^ 2 := hkey
      _ = w t * (Real.exp (2 * K * (t - a)) * ‖h.rep a‖ ^ 2) := by ring
  exact le_of_mul_le_mul_left hkey' hwt

end Energy

/-! ## The weak Laplacian on `H¹` and the coercive bound -/

/-- `L` is the Laplacian of `F ∈ H¹` in the weak `H¹` sense:
`⟨L, G⟩ = -∑ᵢ ⟨∂ᵢF, ∂ᵢG⟩` for every `G ∈ H¹`. -/
def HasWeakLaplacian (F : H1) (L : L2Space) : Prop :=
  ∀ G : H1, inner ℝ L G.value = -∑ i : Fin 3, inner ℝ (F.derivative i) (G.derivative i)

theorem hasWeakLaplacian_h2 (W : H2) : HasWeakLaplacian (h2ToH1 W) (H2.laplace W) := by
  intro G
  rw [H2.laplace_eq, sum_inner, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact weakDerivative_inner (W.first i) (W.second i i) G.value (G.derivative i) i
    (W.hasWeakSecond i i) (G.hasWeakDerivative i)

theorem HasWeakLaplacian.sub {F₁ F₂ : H1} {L₁ L₂ : L2Space} (h₁ : HasWeakLaplacian F₁ L₁)
    (h₂ : HasWeakLaplacian F₂ L₂) : HasWeakLaplacian (F₁ - F₂) (L₁ - L₂) := by
  intro G
  rw [inner_sub_left, h₁ G, h₂ G]
  have hd : ∀ i, (F₁ - F₂).derivative i = F₁.derivative i - F₂.derivative i := fun i =>
    map_sub (H1.derivativeCLM i) F₁ F₂
  simp only [hd, inner_sub_left, Finset.sum_sub_distrib]
  ring

theorem HasWeakLaplacian.smul {F : H1} {L : L2Space} (h : HasWeakLaplacian F L) (a : ℝ) :
    HasWeakLaplacian (a • F) (a • L) := by
  intro G
  rw [real_inner_smul_left, h G]
  have hd : ∀ i, (a • F).derivative i = a • F.derivative i := fun i =>
    map_smul (H1.derivativeCLM i) a F
  simp only [hd, real_inner_smul_left, ← Finset.mul_sum]
  ring

/-- The scalar inequality behind the energy estimate: with `A² = m² + N`,
`-hN + MAm ≤ (M + M²/(4h)) m²`. -/
theorem young_energy {h M A m N : ℝ} (hh : 0 < h) (hM : 0 ≤ M) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hAN : A ^ 2 = m ^ 2 + N) (hN : 0 ≤ N) :
    -(h * N) + M * A * m ≤ (M + M ^ 2 / (4 * h)) * m ^ 2 := by
  have hAm : m ≤ A := by nlinarith
  have hkey : 4 * h * (-(h * N) + M * A * m) ≤ 4 * h * M * m ^ 2 + M ^ 2 * m ^ 2 := by
    have hN' : N = A ^ 2 - m ^ 2 := by linarith
    rw [hN']
    nlinarith [sq_nonneg (2 * h * (A - m) - M * m), mul_nonneg (sub_nonneg.mpr hAm) hm,
      mul_pos hh hh]
  have h4 : 0 < 4 * h := by linarith
  rw [← mul_le_mul_iff_of_pos_left h4]
  calc 4 * h * (-(h * N) + M * A * m) ≤ 4 * h * M * m ^ 2 + M ^ 2 * m ^ 2 := hkey
    _ = 4 * h * ((M + M ^ 2 / (4 * h)) * m ^ 2) := by field_simp

/-- **The coercive bound** (B1010; tex lines 313–316 with `loc:eq:coefficient-maps`). For
`δ ∈ X` with weak Laplacian `L`, a bounded `𝓑 : X → L²_div` with `‖𝓑‖ ≤ M` and `h > 0`,
`⟨hL + 𝓑δ - σδ, δ⟩ ≤ (M + M²/(4h) + |σ|)‖δ‖₂²`. -/
theorem inner_le_energy {h M : ℝ} (hh : 0 < h) (δ : X) {L : L2Space}
    (hL : HasWeakLaplacian δ.toH1 L) (B : X →L[ℝ] L2div) (hB : ‖B‖ ≤ M) (σ : ℝ) :
    inner ℝ (h • L + Lclass (B δ) - σ • Xclass δ) (Xclass δ) ≤
      (M + M ^ 2 / (4 * h) + |σ|) * ‖Xclass δ‖ ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg B).trans hB
  set m := ‖Xclass δ‖ with hmdef
  set N := ∑ i : Fin 3, ‖δ.toH1.derivative i‖ ^ 2 with hNdef
  have hN : 0 ≤ N := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hAN : ‖δ‖ ^ 2 = m ^ 2 + N := by
    have h1 : ‖δ‖ = ‖δ.toH1‖ := rfl
    rw [h1, H1.norm_sq]
    rfl
  have hLδ : inner ℝ L (Xclass δ) = -N := by
    have := hL δ.toH1
    simp only [real_inner_self_eq_norm_sq] at this
    exact this
  have hBδ : inner ℝ (Lclass (B δ)) (Xclass δ) ≤ M * ‖δ‖ * m := by
    calc inner ℝ (Lclass (B δ)) (Xclass δ) ≤ ‖Lclass (B δ)‖ * m := real_inner_le_norm _ _
      _ = ‖B δ‖ * m := rfl
      _ ≤ (M * ‖δ‖) * m := by
          gcongr
          exact (B.le_opNorm δ).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hσ : -(σ * m ^ 2) ≤ |σ| * m ^ 2 := by
    have := neg_abs_le σ
    nlinarith [sq_nonneg m]
  have hY := young_energy hh hM (norm_nonneg _) (norm_nonneg δ) hAN hN
  rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hLδ,
    real_inner_self_eq_norm_sq]
  have hhN : h * -N = -(h * N) := by ring
  rw [hhN]
  nlinarith [hBδ, hY, hσ]

end UnforcedLeray.Blueprint.ModeId
