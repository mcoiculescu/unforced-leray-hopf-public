import UnforcedLeray.Lib.EvolutionFamilies.Fubini

/-!
# Weak generators on a dual core (INF08 T8.7)

Scoping note `scoping/INF07-INF08-INF09-Evolution.md`, §5, target T8.7 (`paper/main.tex`,
lines 1710 (B0111: "testing the weak equation against `q^†` gives `(PU_β)' = -PU_β`"), and the
weak forms `d/ds⟨w,φ⟩ = ⟨w, νΔφ + V·∇φ⟩` of Sections 4 and 6; blueprint B0111, B0115, B0318,
B0324, B0341).

* `EvolutionFamily.HasWeakGenerator E D G`: for every functional `ℓ` in the core `D`,
  `t ↦ ℓ(E(t,s)x)` is differentiable within `[s,b]` with derivative `G t ℓ (E(t,s)x)`.
* `EvolutionFamily.integral_form`: the integrated form
  `ℓ(E(t,r)y) = ℓ(y) + ∫_r^t G τ ℓ (E(τ,r)y) dτ`.
* `dyson_hasWeakGenerator`: the Dyson evolution has the weak generator `G t ℓ + ℓ ∘ A(t)`.
* `EvolutionFamily.proj_evolution_of_left_eig`: a left eigenfunctional with `G t φ = c(t) φ`
  evolves by `φ(E(t,s)x) = exp(∫_s^t c) φ(x)` (this gives `U P = P U` for rank-one `P`).
* `EvolutionFamily.deriv_moving_functional`: for a norm-differentiable family `ℓ(t) ∈ D`,
  `d/dt ℓ(t)(E(t,s)x) = (ℓ'(t) + G t (ℓ t))(E(t,s)x)`.

Hypotheses beyond the scoping signature, all explicit: `t ↦ G t ℓ` is norm-continuous on
`[a,b]` for `ℓ ∈ D` (needed for the integrated form; it holds in every instance listed by the
scoping note, where `G t ℓ` is a fixed operator or depends continuously on the background), and,
in `dyson_hasWeakGenerator`, `A` is norm-continuous on `[a,b]` (the scoping signature's
`ContinuousOn A.A (Icc a b)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {a b : ℝ}

/-- Fundamental theorem of calculus within `[s,b]` for a continuous integrand. -/
theorem hasDerivWithinAt_integral_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} {s b t : ℝ} (hg : ContinuousOn g (Icc s b))
    (ht : t ∈ Icc s b) : HasDerivWithinAt (fun u => ∫ x in s..u, g x) (g t) (Icc s b) t := by
  have : Fact (t ∈ Icc s b) := ⟨ht⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hg.mono (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)).intervalIntegrable)
    (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hg t ht)

theorem ContinuousLinearMap.intervalIntegrable_comp' {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (L : E →L[ℂ] F) {f : ℝ → E}
    {s t : ℝ} (hf : IntervalIntegrable f volume s t) :
    IntervalIntegrable (fun r => L (f r)) volume s t :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

namespace EvolutionFamily

/-- **Weak generator on a dual core** (INF08 T8.7): for `ℓ ∈ D`, `a ≤ s` and `t ∈ [s,b]`,
`t ↦ ℓ(E(t,s)x)` has derivative `G t ℓ (E(t,s)x)` within `[s,b]`. -/
def HasWeakGenerator (E : EvolutionFamily X a b) (D : Set (X →L[ℂ] ℂ))
    (G : ℝ → (X →L[ℂ] ℂ) → (X →L[ℂ] ℂ)) : Prop :=
  ∀ ℓ ∈ D, ∀ s x, a ≤ s → ∀ t ∈ Set.Icc s b,
    HasDerivWithinAt (fun t => ℓ (E.U t s x)) (G t ℓ (E.U t s x)) (Set.Icc s b) t

variable (E : EvolutionFamily X a b) {D : Set (X →L[ℂ] ℂ)}
  {G : ℝ → (X →L[ℂ] ℂ) → (X →L[ℂ] ℂ)}

/-- **Integrated weak form**: `ℓ(E(t,r)y) = ℓ(y) + ∫_r^t G τ ℓ (E(τ,r)y) dτ`. -/
theorem integral_form (hE : E.HasWeakGenerator D G)
    (hG : ∀ ℓ ∈ D, ContinuousOn (fun t => G t ℓ) (Icc a b)) {ℓ : X →L[ℂ] ℂ} (hℓ : ℓ ∈ D)
    {r t : ℝ} (hr : a ≤ r) (hrt : r ≤ t) (ht : t ≤ b) (y : X) :
    ℓ (E.U t r y) = ℓ y + ∫ τ in r..t, G τ ℓ (E.U τ r y) := by
  have hEc : ContinuousOn (fun τ => E.U τ r y) (Icc r t) :=
    (E.continuousOn_fst hr y).mono (Icc_subset_Icc le_rfl ht)
  have hcont : ContinuousOn (fun τ => ℓ (E.U τ r y)) (Icc r t) :=
    ℓ.continuous.comp_continuousOn hEc
  have hderc : ContinuousOn (fun τ => G τ ℓ (E.U τ r y)) (Icc r t) :=
    ((hG ℓ hℓ).mono (Icc_subset_Icc hr ht)).clm_apply hEc
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hrt hcont
    (fun τ hτ => ?_) (hderc.intervalIntegrable_of_Icc hrt)
  · rw [h, E.apply_diag ⟨hr, hrt.trans ht⟩]
    ring
  · have hd := hE ℓ hℓ r y hr τ ⟨hτ.1.le, hτ.2.le.trans ht⟩
    exact (hd.hasDerivAt (Icc_mem_nhds hτ.1 (hτ.2.trans_le ht))).hasDerivWithinAt

/-- **Evolution of a left eigenfunctional** (INF08 T8.7 `proj_evolution_of_left_eig`; B0111):
if `φ ∈ D` and `G t φ = c(t) φ` on `[a,b]` with `c` continuous, then
`φ(E(t,s)x) = exp(∫_s^t c) φ(x)`. -/
theorem proj_evolution_of_left_eig (hE : E.HasWeakGenerator D G) {φ : X →L[ℂ] ℂ} (hφ : φ ∈ D)
    {c : ℝ → ℂ} (hc : ContinuousOn c (Icc a b)) (hGφ : ∀ t ∈ Icc a b, G t φ = c t • φ)
    {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : X) :
    φ (E.U t s x) = Complex.exp (∫ τ in s..t, c τ) * φ x := by
  have hsb : s ≤ b := hst.trans ht
  have hcs : ContinuousOn c (Icc s b) := hc.mono (Icc_subset_Icc hs le_rfl)
  set f : ℝ → ℂ := fun u => Complex.exp (-∫ τ in s..u, c τ) * φ (E.U u s x) with hf
  have hIc : ContinuousOn (fun u => ∫ τ in s..u, c τ) (Icc s b) := fun u hu =>
    (hasDerivWithinAt_integral_Icc hcs hu).continuousWithinAt
  have hfc : ContinuousOn f (Icc s b) :=
    ((hIc.neg).cexp).mul (φ.continuous.comp_continuousOn (E.continuousOn_fst hs x))
  have hfd : ∀ u ∈ Icc s b, HasDerivWithinAt f 0 (Icc s b) u := by
    intro u hu
    have h1 := ((hasDerivWithinAt_integral_Icc hcs hu).neg).cexp
    have h2 := hE φ hφ s x hs u hu
    rw [hGφ u ⟨hs.trans hu.1, hu.2⟩] at h2
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    rw [smul_apply, smul_eq_mul]
    ring
  have hconst := constant_of_has_deriv_right_zero (hfc.mono (Icc_subset_Icc le_rfl ht))
    (fun u hu => (hfd u ⟨hu.1, hu.2.le.trans ht⟩).mono_of_mem_nhdsWithin ?_) t ⟨hst, le_rfl⟩
  · simp only [hf, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, one_mul] at hconst
    rw [E.apply_diag ⟨hs, hsb⟩] at hconst
    rw [← hconst, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  · exact mem_of_superset (Ico_mem_nhdsGE (hu.2.trans_le ht))
      fun v hv => ⟨hu.1.trans hv.1, hv.2.le⟩

/-- **Derivative along a moving functional** (INF08 T8.7 `deriv_moving_functional`): if
`ℓ(t) ∈ D` and `t ↦ ℓ(t)` has derivative `ℓ'` within `[s,b]` at `t` (in operator norm), then
`d/dt ℓ(t)(E(t,s)x) = ℓ'(E(t,s)x) + G t (ℓ t) (E(t,s)x)` within `[s,b]`. -/
theorem deriv_moving_functional (hE : E.HasWeakGenerator D G) {ℓ : ℝ → X →L[ℂ] ℂ}
    {ℓ' : X →L[ℂ] ℂ} {s t : ℝ} (hs : a ≤ s) (ht : t ∈ Icc s b) (hℓD : ℓ t ∈ D)
    (hℓ : HasDerivWithinAt ℓ ℓ' (Icc s b) t) (x : X) :
    HasDerivWithinAt (fun u => ℓ u (E.U u s x)) (ℓ' (E.U t s x) + G t (ℓ t) (E.U t s x))
      (Icc s b) t := by
  -- `ℓ(u)(w(u)) = (ℓ(u) - ℓ(t))(w(u)) + ℓ(t)(w(u))`
  have hw : ContinuousWithinAt (fun u => E.U u s x) (Icc s b) t := E.continuousOn_fst hs x t ht
  have h2 := hE (ℓ t) hℓD s x hs t ht
  -- the first term: `(ℓ(u) - ℓ(t))(w(u))` has derivative `ℓ'(w(t))` at `t`
  have h1 : HasDerivWithinAt (fun u => (ℓ u - ℓ t) (E.U u s x)) (ℓ' (E.U t s x)) (Icc s b) t := by
    rw [hasDerivWithinAt_iff_isLittleO] at hℓ ⊢
    -- `(ℓ u - ℓ t) (w u) - (u - t) • ℓ' (w t)`
    --   `= (ℓ u - ℓ t - (u - t) • ℓ') (w u) + (u - t) • ℓ' (w u - w t)`
    have hb : ∀ᶠ u in 𝓝[Icc s b] t, ‖E.U u s x‖ ≤ E.M * ‖x‖ :=
      eventually_nhdsWithin_of_forall fun u hu => E.norm_apply_le hs hu.1 hu.2 x
    have hA : (fun u => (ℓ u - ℓ t - (u - t) • ℓ') (E.U u s x)) =o[𝓝[Icc s b] t]
        fun u => u - t := by
      refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
      have hK : 0 < E.M * ‖x‖ + 1 := by have := E.M_nonneg; positivity
      filter_upwards [hℓ.bound (div_pos hε hK), hb] with u hu hbu
      calc ‖(ℓ u - ℓ t - (u - t) • ℓ') (E.U u s x)‖
          ≤ ‖ℓ u - ℓ t - (u - t) • ℓ'‖ * ‖E.U u s x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (ε / (E.M * ‖x‖ + 1) * ‖u - t‖) * (E.M * ‖x‖ + 1) :=
            mul_le_mul hu (hbu.trans (le_add_of_nonneg_right zero_le_one)) (norm_nonneg _)
              (by positivity)
        _ = ε * ‖u - t‖ := by field_simp
    have hB : (fun u => (u - t) • ℓ' (E.U u s x - E.U t s x)) =o[𝓝[Icc s b] t]
        fun u => u - t := by
      have hc : Tendsto (fun u => ℓ' (E.U u s x - E.U t s x)) (𝓝[Icc s b] t) (𝓝 0) := by
        have := (ℓ'.continuous.tendsto _).comp (hw.tendsto.sub_const (E.U t s x))
        simpa only [sub_self, map_zero, Function.comp_def] using this
      refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
      filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.mp hc).eventually
        (gt_mem_nhds hε)] with u hu
      rw [sub_zero] at hu
      rw [norm_smul]
      calc ‖u - t‖ * ‖ℓ' (E.U u s x - E.U t s x)‖ ≤ ‖u - t‖ * ε :=
            mul_le_mul_of_nonneg_left hu.le (norm_nonneg _)
        _ = ε * ‖u - t‖ := mul_comm _ _
    refine (hA.add hB).congr_left fun u => ?_
    simp only [sub_self, zero_apply, sub_zero, sub_apply, smul_apply, map_sub, smul_sub]
    abel
  have h3 := h1.add h2
  refine h3.congr_of_mem (fun u _ => ?_) ht
  show ℓ u (E.U u s x) = (ℓ u - ℓ t) (E.U u s x) + ℓ t (E.U u s x)
  rw [sub_apply]
  abel

end EvolutionFamily

variable [CompleteSpace X]

/-- **Weak generator of the Dyson evolution** (INF08 T8.7 `dyson_hasWeakGenerator`; B0111,
B0115, B0318): if `F` has the weak generator `G` on `D` with `t ↦ G t ℓ` norm-continuous and `A`
is norm-continuous on `[a,b]`, then `dyson F A` has the weak generator `G t ℓ + ℓ ∘ A(t)`. -/
theorem dyson_hasWeakGenerator (F : EvolutionFamily X a b) (A : BoundedPert X a b)
    {D : Set (X →L[ℂ] ℂ)} {G : ℝ → (X →L[ℂ] ℂ) → (X →L[ℂ] ℂ)} (hF : F.HasWeakGenerator D G)
    (hG : ∀ ℓ ∈ D, ContinuousOn (fun t => G t ℓ) (Icc a b)) (hA : ContinuousOn A.A (Icc a b)) :
    (dyson F A).HasWeakGenerator D (fun t ℓ => G t ℓ + ℓ.comp (A.A t)) := by
  intro ℓ hℓ s x hs t ht
  set U := dyson F A with hU
  have hsb : s ≤ b := ht.1.trans ht.2
  have hUc : ContinuousOn (fun τ => U.U τ s x) (Icc s b) := U.continuousOn_fst hs x
  have hvc : ContinuousOn (fun τ => A.A τ (U.U τ s x)) (Icc s b) :=
    (hA.mono (Icc_subset_Icc hs le_rfl)).clm_apply hUc
  have hGs : ContinuousOn (fun τ => G τ ℓ) (Icc s b) := (hG ℓ hℓ).mono (Icc_subset_Icc hs le_rfl)
  set g : ℝ → ℂ := fun τ => G τ ℓ (U.U τ s x) + ℓ (A.A τ (U.U τ s x)) with hg
  have hgc : ContinuousOn g (Icc s b) :=
    (hGs.clm_apply hUc).add (ℓ.continuous.comp_continuousOn hvc)
  have hstar : ∀ u ∈ Icc s b, ℓ (U.U u s x) = ℓ x + ∫ τ in s..u, g τ := by
    intro u hu
    have hsu := hu.1
    have hub := hu.2
    have hUcu : ContinuousOn (fun τ => U.U τ s x) (Icc s u) := hUc.mono (Icc_subset_Icc le_rfl hub)
    have hvcu : ContinuousOn (fun τ => A.A τ (U.U τ s x)) (Icc s u) :=
      hvc.mono (Icc_subset_Icc le_rfl hub)
    have hiF := F.intervalIntegrable_integrand A hs hsu hub hUcu
    -- (1) the left Duhamel identity, tested against `ℓ`
    have h1 : ℓ (U.U u s x) = ℓ (F.U u s x) + ∫ r in s..u, ℓ (F.U u r (A.A r (U.U r s x))) := by
      rw [hU, dyson_left F A ⟨hs, hsu, hub⟩ x, map_add, ← hU, ℓ.intervalIntegral_comp_comm hiF]
    -- (2) the integrated weak form for `F`
    have h2 := F.integral_form hF hG hℓ hs hsu hub x
    -- (3) the integrated weak form inside the Duhamel integral
    have hia : IntervalIntegrable (fun r => ℓ (F.U u r (A.A r (U.U r s x)))) volume s u :=
      ContinuousLinearMap.intervalIntegrable_comp' ℓ hiF
    have hib : IntervalIntegrable (fun r => ℓ (A.A r (U.U r s x))) volume s u :=
      (ℓ.continuous.comp_continuousOn hvcu).intervalIntegrable_of_Icc hsu
    have h3 : (∫ r in s..u, ℓ (F.U u r (A.A r (U.U r s x)))) - ∫ r in s..u, ℓ (A.A r (U.U r s x)) =
        ∫ r in s..u, ∫ τ in r..u, G τ ℓ (F.U τ r (A.A r (U.U r s x))) := by
      rw [← intervalIntegral.integral_sub hia hib]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hsu] at hr
      rw [F.integral_form hF hG hℓ (hs.trans hr.1) hr.2 hub]
      ring
    -- (4) Fubini on the triangle
    have hFv : ContinuousOn (fun p : ℝ × ℝ => F.U p.1 p.2 (A.A p.2 (U.U p.2 s x)))
        {p | s ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ u} := by
      intro p hp
      refine UnforcedLeray.Infra.EvolutionContinuity.continuousWithinAt_clm_apply
        (K := fun p : ℝ × ℝ => F.U p.1 p.2) (fun e => ?_) ⟨F.M, ?_⟩ ?_
      · exact ((F.U_cont e).comp continuous_swap.continuousOn
          fun q hq => ⟨hs.trans hq.1, hq.2.1, hq.2.2.trans hub⟩) p hp
      · exact eventually_nhdsWithin_of_forall fun q hq =>
          F.norm_le (hs.trans hq.1) hq.2.1 (hq.2.2.trans hub)
      · exact (hvc.comp continuous_snd.continuousOn
          fun q hq => ⟨hq.1, hq.2.1.trans (hq.2.2.trans hub)⟩) p hp
    have hΦ : ContinuousOn (fun p : ℝ × ℝ => G p.1 ℓ (F.U p.1 p.2 (A.A p.2 (U.U p.2 s x))))
        {p | s ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ u} :=
      (hGs.comp continuous_fst.continuousOn
        fun q hq => ⟨hq.1.trans hq.2.1, hq.2.2.trans hub⟩).clm_apply hFv
    obtain ⟨KG, hKG⟩ := isCompact_Icc.exists_bound_of_continuousOn hGs
    obtain ⟨Kv, hKv⟩ := isCompact_Icc.exists_bound_of_continuousOn hvc
    have h4 := integral_triangle_swap (X := ℂ) hsu
      (G := fun τ r => G τ ℓ (F.U τ r (A.A r (U.U r s x))))
      (K := KG * (F.M * Kv)) (aestronglyMeasurable_triMeasure_of_continuousOn hΦ)
      (fun τ r hr hrτ hτ => by
        refine ((G τ ℓ).le_opNorm _).trans (mul_le_mul (hKG τ ⟨hr.le.trans hrτ.le, hτ.trans hub⟩)
          ((F.norm_apply_le (hs.trans hr.le) hrτ.le (hτ.trans hub) _).trans
            (mul_le_mul_of_nonneg_left (hKv r ⟨hr.le, hrτ.le.trans (hτ.trans hub)⟩)
              F.M_nonneg)) (norm_nonneg _) ((norm_nonneg _).trans
                (hKG τ ⟨hr.le.trans hrτ.le, hτ.trans hub⟩))))
    -- (5) back to the Dyson evolution
    have hiG : ∀ v : ℝ → X, ContinuousOn v (Icc s u) →
        IntervalIntegrable (fun τ => G τ ℓ (v τ)) volume s u := fun v hv =>
      ((hGs.mono (Icc_subset_Icc le_rfl hub)).clm_apply hv).intervalIntegrable_of_Icc hsu
    have hFsc : ContinuousOn (fun τ => F.U τ s x) (Icc s u) :=
      (F.continuousOn_fst hs x).mono (Icc_subset_Icc le_rfl hub)
    have h5 : ∫ τ in s..u, ∫ r in s..τ, G τ ℓ (F.U τ r (A.A r (U.U r s x))) =
        (∫ τ in s..u, G τ ℓ (U.U τ s x)) - ∫ τ in s..u, G τ ℓ (F.U τ s x) := by
      rw [← intervalIntegral.integral_sub (hiG _ hUcu) (hiG _ hFsc)]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le hsu] at hτ
      rw [(G τ ℓ).intervalIntegral_comp_comm (F.intervalIntegrable_integrand A hs hτ.1
        (hτ.2.trans hub) ((hUc.mono (Icc_subset_Icc le_rfl (hτ.2.trans hub))))), ← map_sub, hU,
        dyson_left F A ⟨hs, hτ.1, hτ.2.trans hub⟩ x, add_sub_cancel_left]
    have hsplit : ∫ τ in s..u, g τ =
        (∫ τ in s..u, G τ ℓ (U.U τ s x)) + ∫ τ in s..u, ℓ (A.A τ (U.U τ s x)) :=
      intervalIntegral.integral_add (hiG _ hUcu) hib
    rw [hsplit, h1, h2]
    have h3' := h3
    rw [← h4, h5] at h3'
    linear_combination h3'
  have hd := (hasDerivWithinAt_integral_Icc hgc ht).const_add (ℓ x)
  have hd' := hd.congr_of_mem (fun u hu => hstar u hu) ht
  exact hd'.congr_deriv rfl

end UnforcedLeray.Evolution
