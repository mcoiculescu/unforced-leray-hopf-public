import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.YRep.Meas

/-!
# A globally regular gated kernel
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal Classical

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The kernel `kk` gated by the phase `h > 0` and a spatial cutoff `b`. -/
def yrGate (b : Space → ℝ) (kk : ℝ → Space → ℝ × Space → Space) :
    ℝ → Space → ℝ × Space → Space :=
  fun h y' e => if 0 < h then b y' • kk h y' e else 0

lemma yr_gate_pos (b : Space → ℝ) (kk : ℝ → Space → ℝ × Space → Space) {h : ℝ} (hh : 0 < h)
    (y' : Space) (e : ℝ × Space) : yrGate b kk h y' e = b y' • kk h y' e := by
  simp [yrGate, hh]

lemma yr_gate_contDiff (b : Space → ℝ) (kk : ℝ → Space → ℝ × Space → Space) (Ω : Set Space)
    (hb : ContDiff ℝ 2 b) (hts : tsupport b ⊆ Ω)
    (hreg : ∀ e : ℝ × Space, ∀ y' ∈ Ω, ∀ h : ℝ, 0 < h →
      ContDiffAt ℝ 2 (fun y'' => kk h y'' e) y' ∧ DifferentiableAt ℝ (fun h' => kk h' y' e) h)
    (e : ℝ × Space) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ 2 (fun y' => yrGate b kk h y' e) := by
  simp only [yr_gate_pos b kk hh]
  rw [contDiff_iff_contDiffAt]
  intro y'
  by_cases hy : y' ∈ tsupport b
  · exact hb.contDiffAt.smul (hreg e y' (hts hy) h hh).1
  · have hev : ∀ᶠ y'' in 𝓝 y', b y'' = 0 :=
      Filter.mem_of_superset ((isClosed_tsupport b).isOpen_compl.mem_nhds hy) fun z hz =>
        image_eq_zero_of_notMem_tsupport hz
    refine (contDiffAt_const (c := (0 : Space))).congr_of_eventuallyEq ?_
    exact hev.mono fun z hz => by simp [hz]

lemma yr_gate_diff_h (b : Space → ℝ) (kk : ℝ → Space → ℝ × Space → Space) (Ω : Set Space)
    (hsupp : ∀ y', b y' ≠ 0 → y' ∈ Ω)
    (hreg : ∀ e : ℝ × Space, ∀ y' ∈ Ω, ∀ h : ℝ, 0 < h →
      ContDiffAt ℝ 2 (fun y'' => kk h y'' e) y' ∧ DifferentiableAt ℝ (fun h' => kk h' y' e) h)
    (e : ℝ × Space) (y' : Space) {h : ℝ} (hh : 0 < h) :
    DifferentiableAt ℝ (fun h' => yrGate b kk h' y' e) h := by
  have hev : (fun h' => yrGate b kk h' y' e) =ᶠ[𝓝 h] fun h' => b y' • kk h' y' e :=
    (eventually_gt_nhds hh).mono fun h' hh' => yr_gate_pos b kk hh' y' e
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  by_cases hy : b y' = 0
  · simp [hy]
  · exact (differentiableAt_const (b y')).smul (hreg e y' (hsupp y' hy) h hh).2

/-- Measurability of the four slice functions needed by `ParamDmuCausal`. -/
lemma yr_gate_meas (b : Space → ℝ) (kk : ℝ → Space → ℝ × Space → Space) (Ω : Set Space)
    (hb : ContDiff ℝ 2 b) (hts : tsupport b ⊆ Ω)
    (hreg : ∀ e : ℝ × Space, ∀ y' ∈ Ω, ∀ h : ℝ, 0 < h →
      ContDiffAt ℝ 2 (fun y'' => kk h y'' e) y' ∧ DifferentiableAt ℝ (fun h' => kk h' y' e) h)
    (hmeas : ∀ y' ∈ Ω, ∀ s : ℝ, Measurable fun e : ℝ × Space =>
      if e.1 < s then kk (s - e.1) y' e else 0) :
    (∀ (s : ℝ) (y' : Space), Measurable fun e : ℝ × Space =>
      if e.1 < s then yrGate b kk (s - e.1) y' e else 0) ∧
    (∀ (τ' : ℝ) (y' : Space), AEStronglyMeasurable (fun e : ℝ × Space =>
      if e.1 < τ' then deriv (fun h => yrGate b kk h y' e) (τ' - e.1) else 0) volume) ∧
    (∀ (τ' : ℝ) (y' : Space), AEStronglyMeasurable (fun e : ℝ × Space =>
      if e.1 < τ' then fderiv ℝ (fun y'' => yrGate b kk (τ' - e.1) y'' e) y' else 0) volume) ∧
    (∀ (τ' : ℝ) (y' : Space), AEStronglyMeasurable (fun e : ℝ × Space =>
      if e.1 < τ' then iteratedFDeriv ℝ 2 (fun y'' => yrGate b kk (τ' - e.1) y'' e) y' else 0)
      volume) := by
  have hsupp : ∀ y', b y' ≠ 0 → y' ∈ Ω := fun y' hy =>
    hts (subset_tsupport _ hy)
  have m1 : ∀ (s : ℝ) (y' : Space), Measurable fun e : ℝ × Space =>
      if e.1 < s then yrGate b kk (s - e.1) y' e else 0 := by
    intro s y'
    by_cases hy : b y' = 0
    · have : (fun e : ℝ × Space => if e.1 < s then yrGate b kk (s - e.1) y' e else 0) =
          fun _ => 0 := by
        funext e
        by_cases h : e.1 < s
        · simp [h, yr_gate_pos b kk (sub_pos.2 h), hy]
        · simp [h]
      rw [this]; exact measurable_const
    · have : (fun e : ℝ × Space => if e.1 < s then yrGate b kk (s - e.1) y' e else 0) =
          fun e => b y' • (if e.1 < s then kk (s - e.1) y' e else 0) := by
        funext e
        by_cases h : e.1 < s
        · simp [h, yr_gate_pos b kk (sub_pos.2 h)]
        · simp [h]
      rw [this]
      exact (hmeas y' (hsupp y' hy) s).const_smul (b y')
  -- the slice function `f p`
  have hS : ∀ τ' : ℝ, MeasurableSet {e : ℝ × Space | e.1 < τ'} := fun τ' =>
    measurableSet_lt measurable_fst measurable_const
  have hfd : ∀ (τ' : ℝ) (p : ℝ × Space), p.1 < τ' → ContDiff ℝ 2
      (fun y'' => yrGate b kk (τ' - p.1) y'' p) := fun τ' p hp =>
    yr_gate_contDiff b kk Ω hb hts hreg p (sub_pos.2 hp)
  refine ⟨m1, ?_, ?_, ?_⟩
  · intro τ' y'
    -- derivative in the phase
    let f : ℝ × Space → ℝ → Space := fun p s =>
      if p.1 < τ' then (if p.1 < s then yrGate b kk (s - p.1) y' p else 0) else 0
    have hd : ∀ p, DifferentiableAt ℝ (f p) τ' := by
      intro p
      by_cases hp : p.1 < τ'
      · have hev : f p =ᶠ[𝓝 τ'] fun s => yrGate b kk (s - p.1) y' p := by
          filter_upwards [eventually_gt_nhds hp] with s hs
          simp [f, hp, show p.1 < s from hs]
        refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
        have := yr_gate_diff_h b kk Ω hsupp hreg p y' (sub_pos.2 hp)
        have h2 := this.comp τ' (differentiableAt_id.sub_const p.1)
        exact h2
      · have : f p = fun _ => 0 := by funext s; simp [f, hp]
        rw [this]; exact differentiableAt_const _
    have hm : ∀ s, Measurable fun p => f p s := by
      intro s
      have : (fun p => f p s) = fun p => if p.1 < τ' then
          (if p.1 < s then yrGate b kk (s - p.1) y' p else 0) else 0 := rfl
      rw [this]
      exact Measurable.ite (hS τ') (m1 s y') measurable_const
    have := yr_meas_deriv f τ' hd hm
    refine this.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp : p.1 < τ'
    · have hev : f p =ᶠ[𝓝 τ'] fun s => yrGate b kk (s - p.1) y' p := by
        filter_upwards [eventually_gt_nhds hp] with s hs
        simp [f, hp, show p.1 < s from hs]
      simp only [hp, if_true]
      rw [hev.deriv_eq]
      exact (deriv_comp_sub_const (fun h => yrGate b kk h y' p) p.1) τ'
    · have : f p = fun _ => 0 := by funext s; simp [f, hp]
      simp [hp, this]
  · intro τ' y'
    let f : ℝ × Space → Space → Space := fun p y'' =>
      if p.1 < τ' then yrGate b kk (τ' - p.1) y'' p else 0
    have hfc : ∀ p, ContDiff ℝ 2 (f p) := by
      intro p
      by_cases hp : p.1 < τ'
      · simpa [f, hp] using hfd τ' p hp
      · have : f p = fun _ => 0 := by funext s; simp [f, hp]
        rw [this]; exact contDiff_const
    have hm : ∀ x, Measurable fun p => f p x := fun x => m1 τ' x
    have := yr_meas_fderiv f y' (fun p => ((hfc p).differentiable (by norm_num)) y') hm
    refine this.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp : p.1 < τ'
    · simp [f, hp]
    · have : f p = fun _ => 0 := by funext s; simp [f, hp]
      simp [hp, this]
  · intro τ' y'
    let f : ℝ × Space → Space → Space := fun p y'' =>
      if p.1 < τ' then yrGate b kk (τ' - p.1) y'' p else 0
    have hfc : ∀ p, ContDiff ℝ 2 (f p) := by
      intro p
      by_cases hp : p.1 < τ'
      · simpa [f, hp] using hfd τ' p hp
      · have : f p = fun _ => 0 := by funext s; simp [f, hp]
        rw [this]; exact contDiff_const
    have hm : ∀ x, Measurable fun p => f p x := fun x => m1 τ' x
    have hm1 : ∀ x, Measurable fun p => fderiv ℝ (f p) x := fun x =>
      yr_meas_fderiv f x (fun p => ((hfc p).differentiable (by norm_num)) x) hm
    have hd1 : ∀ p, DifferentiableAt ℝ (fderiv ℝ (f p)) y' := fun p =>
      (((hfc p).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y'
    have := yr_meas_iter2 volume f y' hd1 hm1
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp : p.1 < τ'
    · simp [f, hp]
    · have : f p = fun _ => 0 := by funext s; simp [f, hp]
      simp [hp, this]

end UnforcedLeray.Short.PartIIIb.Concrete

end
