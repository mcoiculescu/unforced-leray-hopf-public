import UnforcedLeray.Loc.Hyp.ModeIdentification.Phase

/-!
# H-ModeId helpers: forward uniqueness, `e^{στ} b_*` is the `E`-solution (B1010)

Support for `Loc/Hyp/ModeIdentification.lean` (target `ModeIdentificationHyp`,
`paper/main.tex` lines 313–318, blueprint unit B1010).

In the frame `P(τ) = D(-τ)·`, with the normalized `E`-solution
`W(τ) = e^{-σ(τ-s₀)} D(-τ)E(τ,s₀)f₀` (`Wf`) and the continuous representative `β` of the
mode `D(-τ)b_*(τ)` (`Drift.mode_hasWeakDerivTime`), the difference `d = W - β` has a weak time
derivative on every `[a,t] ⊂ (s₀,∞)` and satisfies `⟨d', d⟩ ≤ K‖d‖²` a.e.
(`Energy.inner_le_energy` at almost every phase, `Phase.ae_phase`). The energy decay
`‖d(t)‖² ≤ e^{2K(t-a)}‖d(a)‖²` and `d(a) → 0` as `a ↓ s₀` (when `f₀ = b_*(s₀)`) give `d ≡ 0`
(`frame_eq`). Undoing the frame: `E(τ,s₀)f₀ = e^{σ(τ-s₀)}b_*(τ)` for a.e. `τ > s₀`
(`modeGeneratedByL2_of`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.ModeId

open SobolevGraph
open UnforcedLeray.BochnerTime
open UnforcedLeray.Loc.L02 (dil)

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}

/-- The mode in the frame, `D(-τ)b_*(τ)`. -/
def Pb (D : BackgroundData) (τ : ℝ) : L2Space := dil (-τ) (toL2 (D.bstar τ))

/-- Its weak time derivative, `D(-τ)(driftB(τ) - ½b_*(τ))`. -/
def Pb' (D : BackgroundData) (τ : ℝ) : L2Space :=
  dil (-τ) (toL2 (D.driftB τ) - (1 / 2 : ℝ) • toL2 (D.bstar τ))

/-- The normalized `E`-solution in the frame, `e^{-σ(τ-s₀)} D(-τ)E(τ,s₀)f₀`. -/
def Wf (D : BackgroundData) (ev : Evolution) (s₀ : ℝ) (f₀ : X) (τ : ℝ) : L2Space :=
  Real.exp (-(D.σ * (τ - s₀))) • dil (-τ) (Xclass (ev.E τ s₀ f₀))

/-- Its derivative. -/
def Wf' (D : BackgroundData) (c : Coefficients) (ev : Evolution) (s₀ : ℝ) (f₀ : X) (τ : ℝ) :
    L2Space :=
  dil (-τ) (Real.exp (-(D.σ * (τ - s₀))) • (D.h • H2.laplace (ev.EZ τ s₀ f₀).toH2 +
    Lclass (c.B τ (ev.E τ s₀ f₀)) - D.σ • Xclass (ev.E τ s₀ f₀)))

theorem mode_hasWeakDerivTime' (hD : IsUnstableBackground D) (lo hi : ℝ) :
    HasWeakDerivTime lo hi (Pb D) (Pb' D) :=
  mode_hasWeakDerivTime hD lo hi

theorem continuousOn_E (hev : IsEvolution D c S ev) (s₀ : ℝ) (f₀ : X) :
    ContinuousOn (fun τ => ev.E τ s₀ f₀) (Ici s₀) := by
  have hp : Continuous (fun r : ℝ => (r, s₀)) := continuous_id.prodMk continuous_const
  exact (hev.strongly_continuous f₀).comp hp.continuousOn (fun r hr => hr)

theorem continuousOn_EZ (hD : IsUnstableBackground D) (hc : IsCoefficients D c)
    (hS : IsFreeEvolution D.h S) (hev : IsEvolution D c S ev) (s₀ : ℝ) (f₀ : X) :
    ContinuousOn (fun τ => ev.EZ τ s₀ f₀) (Ioi s₀) := by
  intro τ hτ
  have hτ' : s₀ < τ := hτ
  set s₁ := (s₀ + τ) / 2 with hs₁
  have h01 : s₀ < s₁ := by rw [hs₁]; linarith
  have h1τ : s₁ < τ := by rw [hs₁]; linarith
  have hZ := L04.evolutionZContinuity_of hD hc hS hev s₁ (ev.EZ s₁ s₀ f₀)
  have heq : (fun r => ev.EZ r s₁ (ιZ (ev.EZ s₁ s₀ f₀))) =ᶠ[𝓝 τ] fun r => ev.EZ r s₀ f₀ := by
    filter_upwards [Ioi_mem_nhds h1τ] with r hr
    apply L04.ιZ_injective
    rw [L04.EZ_apply hev hr, L04.EZ_apply hev (h01.trans hr), L04.EZ_apply hev h01,
      ← L04.E_apply_law hev h01.le (le_of_lt hr)]
  exact ((hZ.continuousAt (Ioi_mem_nhds h1τ)).congr heq).continuousWithinAt

theorem continuousOn_Wf (hev : IsEvolution D c S ev) (s₀ : ℝ) (f₀ : X) :
    ContinuousOn (Wf D ev s₀ f₀) (Ici s₀) := by
  have h1 : ContinuousOn (fun τ => Xclass (ev.E τ s₀ f₀)) (Ici s₀) :=
    L04.continuous_Xclass.comp_continuousOn (continuousOn_E hev s₀ f₀)
  have h2 := continuousOn_dil_path (k := fun τ => -τ) continuous_neg h1
  have he : Continuous (fun τ : ℝ => Real.exp (-(D.σ * (τ - s₀)))) := by fun_prop
  exact he.continuousOn.smul h2

theorem continuousOn_Wf' (hD : IsUnstableBackground D) (hc : IsCoefficients D c)
    (hS : IsFreeEvolution D.h S) (hev : IsEvolution D c S ev) (s₀ : ℝ) (f₀ : X) :
    ContinuousOn (Wf' D c ev s₀ f₀) (Ioi s₀) := by
  have hZ := continuousOn_EZ hD hc hS hev s₀ f₀
  have hE : ContinuousOn (fun τ => ev.E τ s₀ f₀) (Ioi s₀) :=
    (continuousOn_E hev s₀ f₀).mono Ioi_subset_Ici_self
  have h1 : ContinuousOn (fun τ => H2.laplace (ev.EZ τ s₀ f₀).toH2) (Ioi s₀) :=
    continuous_laplace_toH2.comp_continuousOn hZ
  have h2 : ContinuousOn (fun τ => c.B τ (ev.E τ s₀ f₀)) (Ioi s₀) :=
    hc.B_continuous.continuousOn.clm_apply hE
  have h3 : ContinuousOn (fun τ => D.h • H2.laplace (ev.EZ τ s₀ f₀).toH2 +
      Lclass (c.B τ (ev.E τ s₀ f₀)) - D.σ • Xclass (ev.E τ s₀ f₀)) (Ioi s₀) :=
    ((h1.const_smul D.h).add (continuous_Lclass.comp_continuousOn h2)).sub
      ((L04.continuous_Xclass.comp_continuousOn hE).const_smul D.σ)
  have he : Continuous (fun τ : ℝ => Real.exp (-(D.σ * (τ - s₀)))) := by fun_prop
  exact continuousOn_dil_path (k := fun τ => -τ) continuous_neg (he.continuousOn.smul h3)

theorem Wf_hasDerivAt (hW : L13.EvolutionWeakForm) (hD : IsUnstableBackground D)
    (hc : IsCoefficients D c) (hS : IsFreeEvolution D.h S) (hev : IsEvolution D c S ev)
    (s₀ : ℝ) (f₀ : X) {τ : ℝ} (hτ : s₀ < τ) :
    HasDerivAt (Wf D ev s₀ f₀) (Wf' D c ev s₀ f₀ τ) τ := by
  have hE := evolution_frame_hasDerivAt hW hD hc hS hev s₀ f₀ hτ
  have hexp : HasDerivAt (fun σ : ℝ => Real.exp (-(D.σ * (σ - s₀))))
      (Real.exp (-(D.σ * (τ - s₀))) * (-(D.σ * 1))) τ :=
    ((((hasDerivAt_id τ).sub_const s₀).const_mul D.σ).neg).exp
  have h := hexp.smul hE
  refine h.congr_deriv ?_
  simp only [Wf', map_smul, map_sub, map_add]
  module

theorem Xclass_sub' (f g : X) : Xclass (f - g) = Xclass f - Xclass g :=
  map_sub L13.XclassCLM f g

theorem Xclass_smul' (a : ℝ) (f : X) : Xclass (a • f) = a • Xclass f :=
  map_smul L13.XclassCLM a f

theorem Lclass_sub' (F G : L2div) : Lclass (F - G) = Lclass F - Lclass G :=
  map_sub L13.LclassCLM F G

theorem Lclass_smul' (a : ℝ) (F : L2div) : Lclass (a • F) = a • Lclass F :=
  map_smul L13.LclassCLM a F

theorem alg_identity {V : Type*} [AddCommGroup V] [Module ℝ V] (e h σ : ℝ)
    (A B Cx l b LB : V) :
    e • (h • A + B - σ • Cx) - (h • l - σ • b + LB) =
      h • (e • A - l) + (e • B - LB) - σ • (e • Cx - b) := by
  module

/-- **The coercive bound at one phase** (B1010): at a phase `r > s₀` where the mode is an
`X`-field `b̃` with weak Laplacian `lapB(r)` satisfying the mode equation,
`⟨W' - P_b', W - P_b⟩ ≤ K‖W - P_b‖²` with `K = M + M²/(4h) + |σ|`. -/
theorem phase_bound (hD : IsUnstableBackground D) {M : ℝ} (hM : ∀ τ, ‖c.B τ‖ ≤ M)
    (hev : IsEvolution D c S ev) {s₀ r : ℝ} (hr0 : s₀ < r) (f₀ bt : X)
    (hbt : Xclass bt = toL2 (D.bstar r)) (hbtL : HasWeakLaplacian bt.toH1 (toL2 (D.lapB r)))
    (hmode : toL2 (D.driftB r) - (1 / 2 : ℝ) • toL2 (D.bstar r) =
      D.h • toL2 (D.lapB r) - D.σ • toL2 (D.bstar r) + Lclass (c.B r bt)) :
    inner ℝ (Wf' D c ev s₀ f₀ r - Pb' D r) (Wf D ev s₀ f₀ r - Pb D r) ≤
      (M + M ^ 2 / (4 * D.h) + |D.σ|) * ‖Wf D ev s₀ f₀ r - Pb D r‖ ^ 2 := by
  have hh : 0 < D.h := hD.1.h_pos
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = Real.exp (-(D.σ * (r - s₀))) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Z, w = ev.EZ r s₀ f₀ := ⟨_, rfl⟩
  have hwE : ιZ w = ev.E r s₀ f₀ := by rw [hw]; exact L04.EZ_apply hev hr0 f₀
  obtain ⟨δ, hδ⟩ : ∃ δ : X, δ = e • ιZ w - bt := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : L2Space, L = e • H2.laplace w.toH2 - toL2 (D.lapB r) := ⟨_, rfl⟩
  have hδL : HasWeakLaplacian δ.toH1 L := by
    rw [hδ, hL]
    exact ((hasWeakLaplacian_h2 w.toH2).smul e).sub hbtL
  have hXδ : Xclass δ = e • Xclass (ev.E r s₀ f₀) - toL2 (D.bstar r) := by
    rw [hδ, Xclass_sub', Xclass_smul', hwE, hbt]
  have hBδ : Lclass (c.B r δ) =
      e • Lclass (c.B r (ev.E r s₀ f₀)) - Lclass (c.B r bt) := by
    rw [hδ, map_sub, map_smul, hwE, Lclass_sub', Lclass_smul']
  have hd' : Wf' D c ev s₀ f₀ r - Pb' D r =
      dil (-r) (D.h • L + Lclass (c.B r δ) - D.σ • Xclass δ) := by
    have h1 : Wf' D c ev s₀ f₀ r = dil (-r) (e • (D.h • H2.laplace w.toH2 +
        Lclass (c.B r (ev.E r s₀ f₀)) - D.σ • Xclass (ev.E r s₀ f₀))) := by
      rw [Wf', he, hw]
    have h2 : Pb' D r = dil (-r) (D.h • toL2 (D.lapB r) - D.σ • toL2 (D.bstar r) +
        Lclass (c.B r bt)) := by
      rw [Pb', hmode]
    rw [h1, h2, ← map_sub, hBδ, hXδ, hL, alg_identity]
  have hd : Wf D ev s₀ f₀ r - Pb D r = dil (-r) (Xclass δ) := by
    rw [Wf, Pb, hXδ, map_sub, map_smul, he]
  rw [hd', hd, inner_dil_dil, norm_dil_sq]
  have hle := inner_le_energy hh δ hδL (c.B r) (hM r) D.σ
  have hexp : 0 < Real.exp (-(-r) / 2) := Real.exp_pos _
  calc Real.exp (-(-r) / 2) * inner ℝ (D.h • L + Lclass (c.B r δ) - D.σ • Xclass δ) (Xclass δ)
      ≤ Real.exp (-(-r) / 2) * ((M + M ^ 2 / (4 * D.h) + |D.σ|) * ‖Xclass δ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hle hexp.le
    _ = (M + M ^ 2 / (4 * D.h) + |D.σ|) * (Real.exp (-(-r) / 2) * ‖Xclass δ‖ ^ 2) := by ring

/-- **Energy decay on `[a,t] ⊂ (s₀, hi)`** for `W - β`, `β` the continuous representative of
the mode in the frame on `(lo, hi)`. -/
theorem energy_interval (hW : L13.EvolutionWeakForm) (hR : LaplacianH1Regularity)
    (hD : IsUnstableBackground D) (hc : IsCoefficients D c) (hS : IsFreeEvolution D.h S)
    (hev : IsEvolution D c S ev) {M : ℝ} (hM : ∀ τ, ‖c.B τ‖ ≤ M) {lo hi s₀ : ℝ}
    (hlo : lo < s₀) (f₀ : X) {a t : ℝ} (ha : s₀ < a) (hat : a < t) (hthi : t < hi) :
    ‖Wf D ev s₀ f₀ t - (mode_hasWeakDerivTime' hD lo hi).rep t‖ ^ 2 ≤
      Real.exp (2 * (M + M ^ 2 / (4 * D.h) + |D.σ|) * (t - a)) *
        ‖Wf D ev s₀ f₀ a - (mode_hasWeakDerivTime' hD lo hi).rep a‖ ^ 2 := by
  obtain ⟨H, hH⟩ : ∃ H : HasWeakDerivTime lo hi (Pb D) (Pb' D),
      H = mode_hasWeakDerivTime' hD lo hi := ⟨_, rfl⟩
  rw [← hH]
  have hsub : Icc a t ⊆ Icc lo hi := Icc_subset_Icc (by linarith) hthi.le
  have hWw : HasWeakDerivTime a t (Wf D ev s₀ f₀) (Wf' D c ev s₀ f₀) :=
    hasWeakDerivTime_of_hasDerivAt ((continuousOn_Wf hev s₀ f₀).mono
      (fun r hr => le_of_lt (lt_of_lt_of_le ha hr.1)))
      (fun r hr => Wf_hasDerivAt hW hD hc hS hev s₀ f₀ (ha.trans hr.1))
      ((continuousOn_Wf' hD hc hS hev s₀ f₀).mono (fun r hr => lt_of_lt_of_le ha hr.1))
  have hPw : HasWeakDerivTime a t (Pb D) (Pb' D) := hasWeakDerivTime_mono H (by linarith) hthi.le
  have hdw : HasWeakDerivTime a t (fun r => Wf D ev s₀ f₀ r - Pb D r)
      (fun r => Wf' D c ev s₀ f₀ r - Pb' D r) := by
    refine (hWw.add (hPw.const_smul (-1))).congr_ae ?_ ?_ <;>
      exact Eventually.of_forall (fun r => by simp only [neg_one_smul, ← sub_eq_add_neg])
  have hK : ∀ᵐ r ∂(volume.restrict (Ioo a t)),
      inner ℝ (Wf' D c ev s₀ f₀ r - Pb' D r) (Wf D ev s₀ f₀ r - Pb D r) ≤
        (M + M ^ 2 / (4 * D.h) + |D.σ|) * ‖Wf D ev s₀ f₀ r - Pb D r‖ ^ 2 := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [ae_phase hR hD hc] with r hph hr
    obtain ⟨_, bt, hbt, hbtL, hmode⟩ := hph
    exact phase_bound hD hM hev (ha.trans hr.1) f₀ bt hbt hbtL hmode
  have hdec := energy_decay hdw hK ⟨hat.le, le_rfl⟩
  have hrep : EqOn (fun r => Wf D ev s₀ f₀ r - H.rep r) hdw.rep (Icc a t) := by
    refine hdw.eqOn_rep hat ?_ ?_
    · exact ((continuousOn_Wf hev s₀ f₀).mono
        (fun r hr => le_of_lt (lt_of_lt_of_le ha hr.1))).sub (H.continuousOn_rep.mono hsub)
    · have h1 := ae_restrict_of_ae_restrict_of_subset
        (Ioo_subset_Ioo (show lo ≤ a by linarith) hthi.le) H.ae_eq_rep
      filter_upwards [h1] with r hr
      simp only [hr]
  rw [← hrep ⟨hat.le, le_rfl⟩, ← hrep ⟨le_rfl, hat.le⟩] at hdec
  exact hdec

/-- **Forward uniqueness** (B1010): the `E`-solution and the mode agree in the frame on
`(s₀, hi)`, given equal data at `s₀`. -/
theorem frame_eq (hW : L13.EvolutionWeakForm) (hR : LaplacianH1Regularity)
    (hD : IsUnstableBackground D) (hc : IsCoefficients D c) (hS : IsFreeEvolution D.h S)
    (hev : IsEvolution D c S ev) {lo hi s₀ : ℝ} (hlo : lo < s₀) (hhi : s₀ < hi) (f₀ : X)
    (hf₀ : dil (-s₀) (Xclass f₀) = (mode_hasWeakDerivTime' hD lo hi).rep s₀) :
    ∀ t ∈ Ioo s₀ hi, Wf D ev s₀ f₀ t = (mode_hasWeakDerivTime' hD lo hi).rep t := by
  have hP : 0 < D.period := hD.1.period_pos
  obtain ⟨M, hM⟩ := Loc.L03Evolution.exists_norm_le_of_periodic hP.ne' hc.B_periodic
    hc.B_continuous
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = M + M ^ 2 / (4 * D.h) + |D.σ| := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ → L2Space, β = (mode_hasWeakDerivTime' hD lo hi).rep := ⟨_, rfl⟩
  have hβc : ContinuousOn β (Icc lo hi) := by
    rw [hβ]
    exact (mode_hasWeakDerivTime' hD lo hi).continuousOn_rep
  rw [← hβ] at hf₀ ⊢
  intro t ht
  have henergy : ∀ a, s₀ < a → a < t → ‖Wf D ev s₀ f₀ t - β t‖ ^ 2 ≤
      Real.exp (2 * K * (t - a)) * ‖Wf D ev s₀ f₀ a - β a‖ ^ 2 := by
    intro a ha hat
    rw [hβ, hK]
    exact energy_interval hW hR hD hc hS hev hM hlo f₀ ha hat ht.2
  have hW0 : Wf D ev s₀ f₀ s₀ - β s₀ = 0 := by
    have : Wf D ev s₀ f₀ s₀ = dil (-s₀) (Xclass f₀) := by
      rw [Wf, sub_self, mul_zero, neg_zero, Real.exp_zero, one_smul, hev.at_diag]
      rfl
    rw [this, hf₀, sub_self]
  have hcont : ContinuousWithinAt (fun a => Real.exp (2 * K * (t - a)) *
      ‖Wf D ev s₀ f₀ a - β a‖ ^ 2) (Ioi s₀) s₀ := by
    have h1 : ContinuousWithinAt (Wf D ev s₀ f₀) (Ioi s₀) s₀ :=
      ((continuousOn_Wf hev s₀ f₀) s₀ (Set.mem_Ici.mpr le_rfl)).mono Ioi_subset_Ici_self
    have h2 : ContinuousWithinAt β (Ioi s₀) s₀ :=
      (hβc.continuousAt (Icc_mem_nhds hlo hhi)).continuousWithinAt
    have h3 : Continuous (fun a : ℝ => Real.exp (2 * K * (t - a))) := by fun_prop
    exact h3.continuousWithinAt.mul ((h1.sub h2).norm.pow 2)
  have hlim : Tendsto (fun a => Real.exp (2 * K * (t - a)) *
      ‖Wf D ev s₀ f₀ a - β a‖ ^ 2) (𝓝[>] s₀) (𝓝 0) := by
    have := hcont.tendsto
    rw [hW0, norm_zero] at this
    simpa using this
  have hev2 : ∀ᶠ a in 𝓝[>] s₀, ‖Wf D ev s₀ f₀ t - β t‖ ^ 2 ≤
      Real.exp (2 * K * (t - a)) * ‖Wf D ev s₀ f₀ a - β a‖ ^ 2 := by
    filter_upwards [Ioo_mem_nhdsGT ht.1] with a ha
    exact henergy a ha.1 ha.2
  have h0 : ‖Wf D ev s₀ f₀ t - β t‖ ^ 2 ≤ 0 := ge_of_tendsto hlim hev2
  have h00 : ‖Wf D ev s₀ f₀ t - β t‖ = 0 := by
    nlinarith [norm_nonneg (Wf D ev s₀ f₀ t - β t)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h00)

end UnforcedLeray.Blueprint.ModeId
