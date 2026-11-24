import Mathlib.Topology.Instances.AddCircle.Defs
import UnforcedLeray.Infra.VolterraEvolution.Operator

/-!
# Strong continuity of an evolution family in both time arguments

Abstract form of the phrase "Volterra iteration … constructs a jointly strongly continuous
evolution `E(τ,s)`" (`paper/main.tex`, lines 292-296), and of the continuity of the kernels
`E(τ,s) Π(s)` that the half-line Green operator (lines 406-428) integrates in `s`.

Setting: `E : ℝ → ℝ → (X →L[𝕜] X)` with (`ForwardEvolution E`)

* the evolution law `E(τ,r) E(r,s) = E(τ,s)` for `s ≤ r ≤ τ`;
* boundedness on every strip of bounded elapsed time: `‖E(τ,s)‖ ≤ C_T` for `s ≤ τ ≤ s + T`;
* strong continuity in the later time: `τ ↦ E(τ,s) x` continuous on `[s, ∞)`;
* strong continuity at the diagonal, uniformly in the base point:
  `E(τ,s) x → x` as `(τ,s) → (t,t)` with `s ≤ τ`.

The last hypothesis is what the short-time estimate `‖E(τ,s) - S₀(τ-s)‖ ≤ C (τ-s)^{1/2}` and the
strong continuity of `S₀` at `0` give for the Volterra evolution
(`EvolutionContinuity/Volterra.lean`).

Results:

* `ForwardEvolution.apply_self`: `E(t,t) = 1`;
* (a) `ForwardEvolution.continuousOn_snd`: `s ↦ E(τ,s) x` is continuous on `(-∞, τ]`
  (left of `s₀`: `E(τ,s) = E(τ,s₀) E(s₀,s)` and the diagonal; right of `s₀`:
  `E(τ,s) x - E(τ,s₀) x = E(τ,s)(x - E(s,s₀) x)`);
* (b) `ForwardEvolution.continuousOn`: `(τ,s) ↦ E(τ,s) x` is continuous on `{s ≤ τ}`
  (off the diagonal: `E(τ,s) = E(τ,r) E(r,s)` with a fixed intermediate time `r`);
* (c) `ForwardEvolution.continuousOn_apply`, `continuousOn_comp`, `continuousOn_snd_comp`:
  `(τ,s) ↦ E(τ,s) v(τ,s)` for continuous `v`, in particular `s ↦ E(τ,s) Π(s) x` for a strongly
  continuous family `Π`;
* periodic families: `continuous_of_periodic` (a `P`-periodic function continuous on `[0, P]` is
  continuous; this is where `Π(0) = Π(P)` enters, through `AddCircle.liftIco_continuous`),
  `continuous_apply_of_periodic`, `ForwardEvolution.continuousOn_snd_comp_periodic`;
* `ForwardEvolution.of_continuousOn`: conversely, joint strong continuity, the evolution law,
  `E(t,t) = 1` and the strip bounds give `ForwardEvolution`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Infra.EvolutionContinuity

open UnforcedLeray.Infra.VolterraEvolution (continuousOn_clm_apply)

/-! ### Operator families applied to moving vectors -/

/-- Filter form of strong convergence along a moving vector: if `K t v₀ → w`, `‖K t‖` is
eventually bounded and `v t → v₀`, then `K t (v t) → w`. -/
theorem tendsto_clm_apply {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {l : Filter α} {K : α → E →L[𝕜] F} {v : α → E} {v₀ : E} {w : F}
    (hK : Tendsto (fun t => K t v₀) l (𝓝 w)) (hb : ∃ C, ∀ᶠ t in l, ‖K t‖ ≤ C)
    (hv : Tendsto v l (𝓝 v₀)) : Tendsto (fun t => K t (v t)) l (𝓝 w) := by
  obtain ⟨C, hC⟩ := hb
  have hv0 : Tendsto (fun t => ‖v t - v₀‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hv
  have h2 : Tendsto (fun t => K t (v t) - K t v₀) l (𝓝 0) := by
    have hC0 : Tendsto (fun t => C * ‖v t - v₀‖) l (𝓝 0) := by
      have := hv0.const_mul C
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hC0
    filter_upwards [hC] with t ht
    rw [← map_sub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  have := h2.add hK
  simp only [sub_add_cancel, zero_add] at this
  exact this

/-- Pointwise form of `continuousOn_clm_apply`: strong continuity within `U` at `t₀`, a local
operator-norm bound and continuity of `v` give continuity of `t ↦ K t (v t)` within `U` at
`t₀`. -/
theorem continuousWithinAt_clm_apply {α 𝕜 E F : Type*} [TopologicalSpace α]
    [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {K : α → E →L[𝕜] F} {v : α → E} {U : Set α}
    {t₀ : α} (hK : ∀ e, ContinuousWithinAt (fun t => K t e) U t₀)
    (hb : ∃ C, ∀ᶠ t in 𝓝[U] t₀, ‖K t‖ ≤ C) (hv : ContinuousWithinAt v U t₀) :
    ContinuousWithinAt (fun t => K t (v t)) U t₀ :=
  tendsto_clm_apply (hK (v t₀)) hb hv

/-! ### Periodic functions -/

/-- **Continuity across the period seam.** A `P`-periodic function which is continuous on one
closed period `[0, P]` is continuous on `ℝ` (the endpoint values agree by periodicity). -/
theorem continuous_of_periodic {α : Type*} [TopologicalSpace α] {f : ℝ → α} {P : ℝ}
    (hP : 0 < P) (hper : ∀ t, f (t + P) = f t) (hc : ContinuousOn f (Icc 0 P)) :
    Continuous f := by
  have : Fact (0 < P) := ⟨hP⟩
  have hper' : Function.Periodic f P := hper
  have hf0 : f 0 = f (0 + P) := by rw [hper]
  have hcl : Continuous (AddCircle.liftIco P 0 f) :=
    AddCircle.liftIco_continuous hf0 (by rwa [zero_add])
  have heq : ∀ t : ℝ, f t = AddCircle.liftIco P 0 f (t : AddCircle P) := by
    intro t
    have h1 : ((toIcoMod hP 0 t : ℝ) : AddCircle P) = (t : AddCircle P) := by
      rw [← self_sub_toIcoDiv_zsmul hP 0 t, AddCircle.coe_sub, AddCircle.coe_zsmul,
        AddCircle.coe_period, smul_zero, sub_zero]
    rw [← h1, AddCircle.liftIco_coe_apply (toIcoMod_mem_Ico hP 0 t),
      ← self_sub_toIcoDiv_zsmul hP 0 t, zsmul_eq_mul, hper'.sub_int_mul_eq]
  have hfun : f = AddCircle.liftIco P 0 f ∘ ((↑) : ℝ → AddCircle P) := funext heq
  rw [hfun]
  exact hcl.comp (AddCircle.continuous_mk' P)

/-- A `P`-periodic operator family which is strongly continuous on `[0, P]` is strongly
continuous on `ℝ`. -/
theorem continuous_apply_of_periodic {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Q : ℝ → X →L[𝕜] Y} {P : ℝ} (hP : 0 < P) (hper : ∀ t, Q (t + P) = Q t)
    (hc : ∀ x, ContinuousOn (fun t => Q t x) (Icc 0 P)) (x : X) :
    Continuous fun t => Q t x :=
  continuous_of_periodic hP (fun t => by simp only [hper]) (hc x)

/-! ### Forward evolution families -/

section Evolution

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X : Type*} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

/-- Hypotheses under which a forward evolution family is jointly strongly continuous:
the evolution law, bounds on strips of bounded elapsed time, strong continuity in the later
time, and strong continuity at the diagonal uniformly in the base point. -/
structure ForwardEvolution (E : ℝ → ℝ → X →L[𝕜] X) : Prop where
  comp : ∀ s r τ : ℝ, s ≤ r → r ≤ τ → (E τ r).comp (E r s) = E τ s
  bounded : ∀ T : ℝ, ∃ C : ℝ, ∀ s τ : ℝ, s ≤ τ → τ ≤ s + T → ‖E τ s‖ ≤ C
  continuousOn_fst : ∀ (s : ℝ) (x : X), ContinuousOn (fun τ => E τ s x) (Ici s)
  tendsto_diag : ∀ (t : ℝ) (x : X),
    Tendsto (fun p : ℝ × ℝ => E p.1 p.2 x) (𝓝[{p : ℝ × ℝ | p.2 ≤ p.1}] (t, t)) (𝓝 x)

namespace ForwardEvolution

variable {E : ℝ → ℝ → X →L[𝕜] X}

/-- Joint strong continuity on `{s ≤ τ}`, the evolution law, `E(t,t) = 1` and the strip bounds
give a `ForwardEvolution`. -/
theorem of_continuousOn
    (hcomp : ∀ s r τ : ℝ, s ≤ r → r ≤ τ → (E τ r).comp (E r s) = E τ s)
    (hbd : ∀ T : ℝ, ∃ C : ℝ, ∀ s τ : ℝ, s ≤ τ → τ ≤ s + T → ‖E τ s‖ ≤ C)
    (hself : ∀ t, E t t = 1)
    (hcont : ∀ x, ContinuousOn (fun p : ℝ × ℝ => E p.1 p.2 x) {p : ℝ × ℝ | p.2 ≤ p.1}) :
    ForwardEvolution E where
  comp := hcomp
  bounded := hbd
  continuousOn_fst s x :=
    (hcont x).comp (continuousOn_id.prodMk continuousOn_const) (fun _ hτ => hτ)
  tendsto_diag t x := by
    have h : Tendsto (fun p : ℝ × ℝ => E p.1 p.2 x) (𝓝[{p : ℝ × ℝ | p.2 ≤ p.1}] (t, t))
        (𝓝 (E t t x)) := hcont x (t, t) (le_refl t)
    rwa [hself, one_apply_eq_self] at h

variable (hE : ForwardEvolution E)
include hE

theorem apply_apply {s r τ : ℝ} (hsr : s ≤ r) (hrτ : r ≤ τ) (x : X) :
    E τ r (E r s x) = E τ s x := by
  rw [← ContinuousLinearMap.comp_apply, hE.comp s r τ hsr hrτ]

/-- `E(t,t) x = x`. -/
theorem apply_self (t : ℝ) (x : X) : E t t x = x := by
  have h := (hE.tendsto_diag t x).mono_left
    (pure_le_nhdsWithin (show (t, t) ∈ {p : ℝ × ℝ | p.2 ≤ p.1} from le_refl t))
  exact tendsto_nhds_unique (tendsto_pure_nhds (fun p : ℝ × ℝ => E p.1 p.2 x) (t, t)) h

/-- `E(t,t) = 1`. -/
theorem self_eq (t : ℝ) : E t t = 1 := by
  ext x
  rw [hE.apply_self, one_apply_eq_self]

/-- Local operator-norm bound on the forward cone `{s ≤ τ}`. -/
theorem eventually_norm_le (p₀ : ℝ × ℝ) :
    ∃ C, ∀ᶠ p in 𝓝[{p : ℝ × ℝ | p.2 ≤ p.1}] p₀, ‖E p.1 p.2‖ ≤ C := by
  obtain ⟨C, hC⟩ := hE.bounded (p₀.1 - p₀.2 + 1)
  refine ⟨C, ?_⟩
  have hc : Continuous (fun p : ℝ × ℝ => p.1 - p.2) := continuous_fst.sub continuous_snd
  have h1 : ∀ᶠ p in 𝓝 p₀, (fun p : ℝ × ℝ => p.1 - p.2) p < p₀.1 - p₀.2 + 1 :=
    (hc.tendsto p₀).eventually (gt_mem_nhds (lt_add_one (p₀.1 - p₀.2)))
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with p hp hp'
  have hp1 : p.1 - p.2 < p₀.1 - p₀.2 + 1 := hp
  exact hC p.2 p.1 hp' (by linarith)

/-- Operator-norm bound of `E(τ, r)` for `τ` near `τ₀`, `τ ≥ r`. -/
theorem eventually_norm_fst_le (r τ₀ : ℝ) :
    ∃ C, ∀ᶠ τ in 𝓝 τ₀, r ≤ τ → ‖E τ r‖ ≤ C := by
  obtain ⟨C, hC⟩ := hE.bounded (τ₀ - r + 1)
  refine ⟨C, ?_⟩
  filter_upwards [gt_mem_nhds (lt_add_one τ₀)] with τ hτ hrτ
  exact hC r τ hrτ (by linarith)

/-- Strong continuity at the diagonal from the left: `E(t,s) x → x` as `s ↑ t`. -/
theorem tendsto_left (t : ℝ) (x : X) : Tendsto (fun s => E t s x) (𝓝[≤] t) (𝓝 x) := by
  have h : Tendsto (fun s : ℝ => ((t, s) : ℝ × ℝ)) (𝓝[≤] t)
      (𝓝[{p : ℝ × ℝ | p.2 ≤ p.1}] (t, t)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_const.prodMk continuous_id).tendsto t).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact hs
  exact (hE.tendsto_diag t x).comp h

/-- **(a) Strong continuity in the initial time.** For fixed `τ` and `x`, `s ↦ E(τ,s) x` is
continuous on `(-∞, τ]`. -/
theorem continuousOn_snd (τ : ℝ) (x : X) : ContinuousOn (fun s => E τ s x) (Iic τ) := by
  intro s₀ hs₀
  have hs₀' : s₀ ≤ τ := hs₀
  -- from the left: `E(τ,s) x = E(τ,s₀) (E(s₀,s) x)` and `E(s₀,s) x → x`
  have hL : ContinuousWithinAt (fun s => E τ s x) (Iic s₀) s₀ := by
    have h1 : ContinuousWithinAt (fun s => E s₀ s x) (Iic s₀) s₀ := by
      show Tendsto (fun s => E s₀ s x) (𝓝[Iic s₀] s₀) (𝓝 (E s₀ s₀ x))
      rw [hE.apply_self]
      exact hE.tendsto_left s₀ x
    have h2 : ContinuousWithinAt (fun s => E τ s₀ (E s₀ s x)) (Iic s₀) s₀ :=
      (E τ s₀).continuous.continuousAt.comp_continuousWithinAt h1
    refine h2.congr (fun s hs => ?_) ?_
    · exact (hE.apply_apply hs hs₀' x).symm
    · exact (hE.apply_apply le_rfl hs₀' x).symm
  -- from the right: `E(τ,s) x - E(τ,s₀) x = E(τ,s) (x - E(s,s₀) x)`
  have hR : ContinuousWithinAt (fun s => E τ s x) (Icc s₀ τ) s₀ := by
    obtain ⟨C, hC⟩ := hE.bounded (τ - s₀)
    have hv : Tendsto (fun s => ‖x - E s s₀ x‖) (𝓝[Icc s₀ τ] s₀) (𝓝 0) := by
      have h := (hE.continuousOn_fst s₀ x s₀ self_mem_Ici).mono
        (Icc_subset_Ici_self : Icc s₀ τ ⊆ Ici s₀)
      have h' := tendsto_iff_norm_sub_tendsto_zero.mp h
      simp only [hE.apply_self] at h'
      simpa only [norm_sub_rev] using h'
    have hC0 : Tendsto (fun s => C * ‖x - E s s₀ x‖) (𝓝[Icc s₀ τ] s₀) (𝓝 0) := by
      have := hv.const_mul C
      rwa [mul_zero] at this
    have hd : Tendsto (fun s => E τ s x - E τ s₀ x) (𝓝[Icc s₀ τ] s₀) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hC0
      filter_upwards [self_mem_nhdsWithin] with s hs
      have h3 : E τ s x - E τ s₀ x = E τ s (x - E s s₀ x) := by
        rw [map_sub, hE.apply_apply hs.1 hs.2 x]
      rw [h3]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hC s τ hs.2 (by linarith [hs.1])) (norm_nonneg _))
    exact tendsto_sub_nhds_zero_iff.1 hd
  have hU : Iic τ ⊆ Iic s₀ ∪ Icc s₀ τ := fun s hs => by
    rcases le_total s s₀ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hs⟩
  exact (hL.union hR).mono hU

/-- **(b) Joint strong continuity.** `(τ,s) ↦ E(τ,s) x` is continuous on `{s ≤ τ}`. -/
theorem continuousOn (x : X) :
    ContinuousOn (fun p : ℝ × ℝ => E p.1 p.2 x) {p : ℝ × ℝ | p.2 ≤ p.1} := by
  rintro ⟨τ₀, s₀⟩ hp₀
  have hp₀' : s₀ ≤ τ₀ := hp₀
  rcases hp₀'.eq_or_lt with h | h
  · subst h
    show Tendsto (fun p : ℝ × ℝ => E p.1 p.2 x) (𝓝[{p : ℝ × ℝ | p.2 ≤ p.1}] (s₀, s₀))
      (𝓝 (E s₀ s₀ x))
    rw [hE.apply_self]
    exact hE.tendsto_diag s₀ x
  · set r := (s₀ + τ₀) / 2 with hr
    have hsr : s₀ < r := by linarith
    have hrτ : r < τ₀ := by linarith
    have hWn : Ici r ×ˢ Iic r ∈ 𝓝 (τ₀, s₀) := prod_mem_nhds (Ici_mem_nhds hrτ) (Iic_mem_nhds hsr)
    have hg : ContinuousWithinAt (fun p : ℝ × ℝ => E p.1 r (E r p.2 x)) (Ici r ×ˢ Iic r)
        (τ₀, s₀) := by
      refine continuousWithinAt_clm_apply (K := fun p : ℝ × ℝ => E p.1 r) ?_ ?_ ?_
      · intro e
        have hfst : ContinuousWithinAt (Prod.fst : ℝ × ℝ → ℝ) (Ici r ×ˢ Iic r) (τ₀, s₀) :=
          continuous_fst.continuousWithinAt
        exact ((hE.continuousOn_fst r e) τ₀ hrτ.le).comp hfst
          (fun p (hp : p ∈ Ici r ×ˢ Iic r) => hp.1)
      · obtain ⟨C, hC⟩ := hE.eventually_norm_fst_le r τ₀
        refine ⟨C, ?_⟩
        have h1 : ∀ᶠ p in 𝓝 (τ₀, s₀), r ≤ (p : ℝ × ℝ).1 → ‖E p.1 r‖ ≤ C :=
          (continuous_fst.tendsto (τ₀, s₀)).eventually hC
        filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with p hp hp'
        exact hp hp'.1
      · have hsnd : ContinuousWithinAt (Prod.snd : ℝ × ℝ → ℝ) (Ici r ×ˢ Iic r) (τ₀, s₀) :=
          continuous_snd.continuousWithinAt
        exact ((hE.continuousOn_snd r x) s₀ hsr.le).comp hsnd
          (fun p (hp : p ∈ Ici r ×ˢ Iic r) => hp.2)
    have hg' : ContinuousAt (fun p : ℝ × ℝ => E p.1 r (E r p.2 x)) (τ₀, s₀) :=
      hg.continuousAt hWn
    refine (hg'.congr ?_).continuousWithinAt
    filter_upwards [hWn] with p hp
    exact hE.apply_apply hp.2 hp.1 x

/-- **(c) Joint continuity along moving vectors.** If `v` is continuous on a subset `W` of the
forward cone, `(τ,s) ↦ E(τ,s) v(τ,s)` is continuous on `W`. -/
theorem continuousOn_apply {W : Set (ℝ × ℝ)} (hW : W ⊆ {p : ℝ × ℝ | p.2 ≤ p.1})
    {v : ℝ × ℝ → X} (hv : ContinuousOn v W) :
    ContinuousOn (fun p : ℝ × ℝ => E p.1 p.2 (v p)) W := by
  refine continuousOn_clm_apply (K := fun p : ℝ × ℝ => E p.1 p.2)
    (fun e => (hE.continuousOn e).mono hW) (fun p₀ _ => ?_) hv
  obtain ⟨C, hC⟩ := hE.eventually_norm_le p₀
  exact ⟨C, hC.filter_mono (nhdsWithin_mono p₀ hW)⟩

/-- **(c) Composition with a strongly continuous family `Q`** (`Q = Π₋` in the manuscript):
`(τ,s) ↦ E(τ,s) Q(s) x` is continuous on `{s ≤ τ, s ∈ U}` if `s ↦ Q(s) x` is continuous on
`U` for every `x`. -/
theorem continuousOn_comp {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Q : ℝ → Y →L[𝕜] X} {U : Set ℝ} (hQ : ∀ y, ContinuousOn (fun s => Q s y) U) (y : Y) :
    ContinuousOn (fun p : ℝ × ℝ => E p.1 p.2 (Q p.2 y)) {p : ℝ × ℝ | p.2 ≤ p.1 ∧ p.2 ∈ U} :=
  hE.continuousOn_apply (fun _ hp => hp.1)
    ((hQ y).comp continuous_snd.continuousOn (fun _ hp => hp.2))

/-- **(c), initial-time form.** `s ↦ E(τ,s) Q(s) x` is continuous on `(-∞, τ] ∩ U`. -/
theorem continuousOn_snd_comp {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Q : ℝ → Y →L[𝕜] X} {U : Set ℝ} (hQ : ∀ y, ContinuousOn (fun s => Q s y) U) (τ : ℝ)
    (y : Y) : ContinuousOn (fun s => E τ s (Q s y)) (Iic τ ∩ U) :=
  (hE.continuousOn_comp hQ y).comp (continuousOn_const.prodMk continuousOn_id)
    (fun _ hs => ⟨hs.1, hs.2⟩)

/-- **(c), joint form for a strongly continuous family on `ℝ`.** -/
theorem continuousOn_comp_univ {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Q : ℝ → Y →L[𝕜] X} (hQ : ∀ y, Continuous (fun s => Q s y)) (y : Y) :
    ContinuousOn (fun p : ℝ × ℝ => E p.1 p.2 (Q p.2 y)) {p : ℝ × ℝ | p.2 ≤ p.1} :=
  (hE.continuousOn_comp (U := univ) (fun y => (hQ y).continuousOn) y).mono
    (fun _ hp => ⟨hp, mem_univ _⟩)

/-- **(c) for periodic families.** If `Q` is `P`-periodic and strongly continuous on `[0, P]`,
then `(τ,s) ↦ E(τ,s) Q(s) x` is continuous on `{s ≤ τ}`. -/
theorem continuousOn_comp_periodic {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Q : ℝ → Y →L[𝕜] X} {P : ℝ} (hP : 0 < P) (hper : ∀ t, Q (t + P) = Q t)
    (hc : ∀ y, ContinuousOn (fun t => Q t y) (Icc 0 P)) (y : Y) :
    ContinuousOn (fun p : ℝ × ℝ => E p.1 p.2 (Q p.2 y)) {p : ℝ × ℝ | p.2 ≤ p.1} :=
  hE.continuousOn_comp_univ (continuous_apply_of_periodic hP hper hc) y

/-- **(c) for periodic families, initial-time form.** -/
theorem continuousOn_snd_comp_periodic {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Q : ℝ → Y →L[𝕜] X} {P : ℝ} (hP : 0 < P) (hper : ∀ t, Q (t + P) = Q t)
    (hc : ∀ y, ContinuousOn (fun t => Q t y) (Icc 0 P)) (τ : ℝ) (y : Y) :
    ContinuousOn (fun s => E τ s (Q s y)) (Iic τ) := by
  have h := hE.continuousOn_snd_comp (U := univ)
    (fun y => (continuous_apply_of_periodic hP hper hc y).continuousOn) τ y
  rwa [inter_univ] at h

/-- Continuity along a fixed elapsed time: `τ ↦ E(τ, τ - r) Q(τ - r) x` is continuous for
`r ≥ 0` (the form of `GreenKernel.TimeContinuous.Km_shift`). -/
theorem continuous_shift {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {Q : ℝ → Y →L[𝕜] X} (hQ : ∀ y, Continuous (fun s => Q s y)) {r : ℝ} (hr : 0 ≤ r)
    (y : Y) : Continuous fun τ => E τ (τ - r) (Q (τ - r) y) := by
  refine (hE.continuousOn_comp_univ hQ y).comp_continuous
    (continuous_id.prodMk (continuous_id.sub continuous_const)) (fun τ => ?_)
  show τ - r ≤ τ
  linarith

end ForwardEvolution

end Evolution

end UnforcedLeray.Infra.EvolutionContinuity
