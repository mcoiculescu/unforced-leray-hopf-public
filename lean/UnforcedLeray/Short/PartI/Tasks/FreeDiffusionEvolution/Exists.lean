import UnforcedLeray.Short.PartI.Sub.C02
import UnforcedLeray.Cons.L2.CanonicalBranch.DysonStage

/-!
# Part I, task `PartI:C02`: existence of the free diffusion evolution

Source of record: `the November 2 reference manuscript`, lines 1019-1021
("the evolution exists for measurable beta by the Dyson series based on exp(D int beta)").

For measurable `0 ≤ β ≤ βs` the candidate is `F t s := U(t,s)` for `s ≤ t`, where `U` is the
Dyson sum on the block `[s,t]` of the Gaussian diffusion family `freeDiffusionFamily β` with the
bounded interaction `T - λ - βκ` (`T = -2iΩ`), and `F t s := 1` for `t < s`. The Dyson sum on
`[s,b]` restricted to `[s,r]`, `r ≤ b`, is the Dyson sum on `[s,r]` because its terms only use
`F.U` and `A.A`, which do not depend on the block.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-! ### Blocks and Dyson families -/

theorem fdeAux_abs_le {β : ℝ → ℝ} {βs : ℝ} (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (τ : ℝ) :
    |β τ| ≤ βs := by
  rw [abs_of_nonneg (hβ τ).1]
  exact (hβ τ).2

theorem fdeAux_intervalIntegrable {β : ℝ → ℝ} {βs : ℝ} (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (s t : ℝ) : IntervalIntegrable β volume s t := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := βs) ?_ hβm.aestronglyMeasurable ?_
  · exact (measure_mono uIoc_subset_uIcc).trans_lt measure_Icc_lt_top |>.ne
  · exact (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun τ _ => by
      rw [Real.norm_eq_abs]; exact fdeAux_abs_le hβ τ)

/-- The Gaussian diffusion family on the block `[s,t]`. -/
def fdeAuxFree (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β) (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs)
    (s t : ℝ) : UnforcedLeray.Evolution.EvolutionFamily B0010.XG s t :=
  UnforcedLeray.Cons.G3b.freeDiffusionFamily β (fdeAux_intervalIntegrable hβm hβ)
    (fun τ => (hβ τ).1) βs (fdeAux_abs_le hβ)

/-- The bounded first-stage interaction `T - λ - βκ` on the block `[s,t]`. -/
def fdeAuxPert (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (s t : ℝ) :
    UnforcedLeray.Evolution.BoundedPert B0010.XG s t :=
  UnforcedLeray.Cons.G3b.transportDysonPert ((-2 * Complex.I) • B0012.omegaOp) lam kappa β s t
    hβm.aestronglyMeasurable ⟨βs, fun τ _ => fdeAux_abs_le hβ τ⟩

/-- The Dyson evolution on the block `[s,t]`. -/
def fdeAuxBlock (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (s t : ℝ) :
    UnforcedLeray.Evolution.EvolutionFamily B0010.XG s t :=
  UnforcedLeray.Evolution.dyson (fdeAuxFree β βs hβm hβ s t)
    (fdeAuxPert lam kappa β βs hβm hβ s t)

theorem fdeAuxBlock_U (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (s t : ℝ) :
    (fdeAuxBlock lam kappa β βs hβm hβ s t).U =
      UnforcedLeray.Evolution.dysonU (fdeAuxFree β βs hβm hβ s t)
        (fdeAuxPert lam kappa β βs hβm hβ s t) :=
  rfl

/-! ### Block independence of the Dyson terms -/

/-- Dyson terms depend only on the coefficient functions `F.U` and `A.A`, not on the block. -/
theorem fdeAux_dysonTerm_congr {a b a' b' : ℝ}
    (F : UnforcedLeray.Evolution.EvolutionFamily B0010.XG a b)
    (A : UnforcedLeray.Evolution.BoundedPert B0010.XG a b)
    (F' : UnforcedLeray.Evolution.EvolutionFamily B0010.XG a' b')
    (A' : UnforcedLeray.Evolution.BoundedPert B0010.XG a' b')
    (hU : ∀ t s, F.U t s = F'.U t s) (hA : ∀ t, A.A t = A'.A t) (k : ℕ) (t s : ℝ)
    (x : B0010.XG) :
    UnforcedLeray.Evolution.dysonTerm F A k t s x =
      UnforcedLeray.Evolution.dysonTerm F' A' k t s x := by
  induction k generalizing t s x with
  | zero => simp only [UnforcedLeray.Evolution.dysonTerm_zero, hU]
  | succ k ih => simp only [UnforcedLeray.Evolution.dysonTerm_succ, hU, hA, ih]

theorem fdeAux_block_indep (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) {s r b : ℝ} (hsr : s ≤ r) (hrb : r ≤ b)
    (x : B0010.XG) :
    (fdeAuxBlock lam kappa β βs hβm hβ s r).U r s x =
      (fdeAuxBlock lam kappa β βs hβm hβ s b).U r s x := by
  rw [fdeAuxBlock_U, fdeAuxBlock_U,
    UnforcedLeray.Evolution.dysonU_apply _ _ (le_refl s) hsr le_rfl x,
    UnforcedLeray.Evolution.dysonU_apply _ _ (le_refl s) hsr hrb x]
  exact tsum_congr fun k => fdeAux_dysonTerm_congr (fdeAuxFree β βs hβm hβ s r)
    (fdeAuxPert lam kappa β βs hβm hβ s r) (fdeAuxFree β βs hβm hβ s b)
    (fdeAuxPert lam kappa β βs hβm hβ s b) (fun _ _ => rfl) (fun _ => rfl) k r s x

/-! ### The candidate evolution -/

/-- The candidate evolution: `F t s = U(t,s)` on the block `[s,t]` for `s ≤ t`, and `1` else. -/
def fdeAuxF (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (t s : ℝ) : B0010.XG →L[ℂ] B0010.XG :=
  if s ≤ t then (fdeAuxBlock lam kappa β βs hβm hβ s t).U t s else 1

theorem fdeAuxF_eq_block (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) {s t b : ℝ} (hst : s ≤ t) (htb : t ≤ b)
    (x : B0010.XG) :
    fdeAuxF lam kappa β βs hβm hβ t s x = (fdeAuxBlock lam kappa β βs hβm hβ s b).U t s x := by
  unfold fdeAuxF
  rw [if_pos hst]
  exact fdeAux_block_indep lam kappa β βs hβm hβ hst htb x

theorem fdeAux_self_eq (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (t : ℝ) :
    fdeAuxF lam kappa β βs hβm hβ t t = 1 := by
  unfold fdeAuxF
  rw [if_pos (le_refl t), fdeAuxBlock_U]
  exact UnforcedLeray.Evolution.dysonU_diag _ _ (Set.left_mem_Icc.mpr le_rfl)

theorem fdeAux_cont (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (x : B0010.XG) (s : ℝ) :
    ContinuousOn (fun t => fdeAuxF lam kappa β βs hβm hβ t s x) (Ici s) := by
  intro t₀ ht₀
  have hst₀ : s ≤ t₀ := Set.mem_Ici.mp ht₀
  have hlt : t₀ < t₀ + 1 := lt_add_one t₀
  have hc : ContinuousOn (fun t => UnforcedLeray.Evolution.dysonU
      (fdeAuxFree β βs hβm hβ s (t₀ + 1)) (fdeAuxPert lam kappa β βs hβm hβ s (t₀ + 1)) t s x)
      (Icc s (t₀ + 1)) :=
    UnforcedLeray.Evolution.continuousOn_dysonU_fst _ _ x (le_refl s)
  have hcongr : ContinuousOn (fun t => fdeAuxF lam kappa β βs hβm hβ t s x)
      (Icc s (t₀ + 1)) := by
    refine hc.congr fun t ht => ?_
    show fdeAuxF lam kappa β βs hβm hβ t s x = UnforcedLeray.Evolution.dysonU
      (fdeAuxFree β βs hβm hβ s (t₀ + 1)) (fdeAuxPert lam kappa β βs hβm hβ s (t₀ + 1)) t s x
    rw [fdeAuxF_eq_block lam kappa β βs hβm hβ ht.1 ht.2 x, fdeAuxBlock_U]
  have hmem : Icc s (t₀ + 1) ∈ 𝓝[Ici s] t₀ :=
    mem_nhdsWithin.mpr ⟨Iio (t₀ + 1), isOpen_Iio, Set.mem_Iio.mpr hlt,
      fun t ht => ⟨Set.mem_Ici.mp ht.2, le_of_lt (Set.mem_Iio.mp ht.1)⟩⟩
  exact (hcongr t₀ ⟨hst₀, hlt.le⟩).mono_of_mem_nhdsWithin hmem

/-! ### Pointwise identities for the integrands -/

theorem fdeAux_pt (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) {s t r : ℝ} (hsr : s ≤ r) (hrt : r ≤ t) (x : B0010.XG) :
    (fdeAuxFree β βs hβm hβ s t).U t r
        ((fdeAuxPert lam kappa β βs hβm hβ s t).A r
          (UnforcedLeray.Evolution.dysonU (fdeAuxFree β βs hβm hβ s t)
            (fdeAuxPert lam kappa β βs hβm hβ s t) r s x)) =
      B0123.expD (∫ u in r..t, β u)
        (freeCoeff lam kappa β r (fdeAuxF lam kappa β βs hβm hβ r s x)) := by
  rw [fdeAuxF_eq_block lam kappa β βs hβm hβ hsr hrt x, fdeAuxBlock_U]
  rfl

theorem fdeAux_pt_duhamel (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) {s t r : ℝ} (hsr : s ≤ r) (hrt : r ≤ t) (x : B0010.XG) :
    (fdeAuxFree β βs hβm hβ s t).U t r
        ((fdeAuxPert lam kappa β βs hβm hβ s t).A r
          ((fdeAuxBlock lam kappa β βs hβm hβ s t).U r s x)) =
      B0123.expD (∫ u in r..t, β u)
        (freeCoeff lam kappa β r (fdeAuxF lam kappa β βs hβm hβ r s x)) := by
  rw [fdeAuxF_eq_block lam kappa β βs hβm hβ hsr hrt x]
  rfl

theorem fdeAux_integrable (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (s t : ℝ) (hst : s ≤ t) (x : B0010.XG) :
    IntervalIntegrable (fun r => B0123.expD (∫ u in r..t, β u)
      (freeCoeff lam kappa β r (fdeAuxF lam kappa β βs hβm hβ r s x))) volume s t := by
  refine (UnforcedLeray.Evolution.intervalIntegrable_dysonU (fdeAuxFree β βs hβm hβ s t)
    (fdeAuxPert lam kappa β βs hβm hβ s t) (le_refl s) hst le_rfl x).congr_ae
    (ae_restrict_of_forall_mem measurableSet_uIoc fun r hr => ?_)
  rw [uIoc_of_le hst] at hr
  exact fdeAux_pt lam kappa β βs hβm hβ hr.1.le hr.2 x

/-- The zeroth Dyson term on the block `[s,t]` is the Gaussian factor `expD (∫_s^t β)`. -/
theorem fdeAux_free_apply (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (s t : ℝ) (x : B0010.XG) :
    (fdeAuxFree β βs hβm hβ s t).U t s x = B0123.expD (∫ u in s..t, β u) x :=
  rfl

theorem fdeAux_duhamel (lam kappa : ℂ) (β : ℝ → ℝ) (βs : ℝ) (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) (s t : ℝ) (hst : s ≤ t) (x : B0010.XG) :
    fdeAuxF lam kappa β βs hβm hβ t s x = B0123.expD (∫ u in s..t, β u) x +
      ∫ r in s..t, B0123.expD (∫ u in r..t, β u)
        (freeCoeff lam kappa β r (fdeAuxF lam kappa β βs hβm hβ r s x)) := by
  have hD : (fdeAuxBlock lam kappa β βs hβm hβ s t).U t s x =
      (fdeAuxFree β βs hβm hβ s t).U t s x + ∫ r in s..t,
        (fdeAuxFree β βs hβm hβ s t).U t r
          ((fdeAuxPert lam kappa β βs hβm hβ s t).A r
            ((fdeAuxBlock lam kappa β βs hβm hβ s t).U r s x)) :=
    UnforcedLeray.Evolution.dyson_left (fdeAuxFree β βs hβm hβ s t)
      (fdeAuxPert lam kappa β βs hβm hβ s t) ⟨le_refl s, hst, le_rfl⟩ x
  rw [fdeAuxF_eq_block lam kappa β βs hβm hβ hst le_rfl x, hD,
    fdeAux_free_apply β βs hβm hβ s t x]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hst] at hr
  exact fdeAux_pt_duhamel lam kappa β βs hβm hβ hr.1 hr.2 x

/-! ### The target -/

/-- **Target `PartI:C02`, sub-lemma 1 (existence)**: for measurable `0 ≤ β ≤ βs` the free
diffusion evolution exists. -/
theorem freeDiffusionEvolutionExists : FreeDiffusionEvolutionExists := by
  unfold FreeDiffusionEvolutionExists
  intro lam kappa βs β hβm hβ
  exact ⟨fdeAuxF lam kappa β βs hβm hβ,
    { self_eq := fun t => fdeAux_self_eq lam kappa β βs hβm hβ t
      cont := fun x s => fdeAux_cont lam kappa β βs hβm hβ x s
      integrable := fun s t hst x => fdeAux_integrable lam kappa β βs hβm hβ s t hst x
      duhamel := fun s t hst x => fdeAux_duhamel lam kappa β βs hβm hβ s t hst x }⟩

end UnforcedLeray.Short.PartI
