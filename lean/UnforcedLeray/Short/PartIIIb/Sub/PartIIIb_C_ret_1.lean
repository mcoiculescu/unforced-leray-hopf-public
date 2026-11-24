import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Sub-lemmas for `PartIII-b:C/ret/1` (Banach space `𝒜`, source lines 4733-4752)

`AffClosure`, `AffNormLaws`, `AffCompleteness` are the three true source facts needed to make
`{A // IsAffElem as A}` a real Banach space with norm `affNorm as`.  `affSub` and the instance
constructors below build the structure from them.
-/

set_option autoImplicit false

noncomputable section

open Set Real Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Closure of `IsAffElem as` under `0`, `+`, scalar multiples (source 4741-4745; the iterated
`s ∂_s` is linear on `C^6` functions on `(0,∞)`, and the norm is finite by the triangle
inequality). -/
def AffClosure (as : ℝ) : Prop :=
  IsAffElem as 0 ∧
  (∀ A B : ℝ → Mat3, IsAffElem as A → IsAffElem as B → IsAffElem as (A + B)) ∧
  (∀ (c : ℝ) (A : ℝ → Mat3), IsAffElem as A → IsAffElem as (c • A))

/-- Norm laws for `affNorm as` on elements of `𝒜` (source 4750): triangle inequality,
absolute homogeneity, and definiteness (norm zero forces `A = 0` on `(0,∞)`, hence everywhere
by `zeroOff`). -/
def AffNormLaws (as : ℝ) : Prop :=
  (∀ A B : ℝ → Mat3, IsAffElem as A → IsAffElem as B →
      affNorm as (A + B) ≤ affNorm as A + affNorm as B) ∧
  (∀ (c : ℝ) (A : ℝ → Mat3), IsAffElem as A → affNorm as (c • A) = |c| * affNorm as A) ∧
  (∀ A : ℝ → Mat3, IsAffElem as A → affNorm as A = 0 → A = 0)

/-- Completeness of `(𝒜, affNorm as)` (source 4733-4752): every `affNorm`-Cauchy sequence of
elements converges to an element.  Proof idea: weight positive on compacts of `(0,∞)` gives local
uniform convergence of each `(s∂_s)^j A_n`, `j ≤ 6`; the limit is `C^6`
(`hasDerivAt_of_tendstoLocallyUniformlyOn`), trace/azimuth conditions are closed, and the bound is
uniform. -/
def AffCompleteness (as : ℝ) : Prop :=
  ∀ f : ℕ → (ℝ → Mat3), (∀ n, IsAffElem as (f n)) →
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, affNorm as (f m - f n) < ε) →
    ∃ A, IsAffElem as A ∧ Tendsto (fun n => affNorm as (f n - A)) atTop (𝓝 0)

/-- The submodule `𝒜 ⊆ (ℝ → Mat3)`. -/
def affSub (as : ℝ) (h : AffClosure as) : Submodule ℝ (ℝ → Mat3) where
  carrier := {A | IsAffElem as A}
  zero_mem' := h.1
  add_mem' := fun {A B} hA hB => h.2.1 A B hA hB
  smul_mem' := fun c A hA => h.2.2 c A hA

lemma affNorm_nonneg_of (as : ℝ) (A : ℝ → Mat3) (hA : IsAffElem as A) : 0 ≤ affNorm as A := by
  unfold affNorm
  have hne : (Ioi (0 : ℝ)).Nonempty := ⟨1, by simp⟩
  obtain ⟨s, hs⟩ := hne
  refine le_trans ?_ (le_csSup hA.bdd ⟨s, hs, rfl⟩)
  unfold affTerm affSum
  have : 0 ≤ Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hs) _)
  refine mul_nonneg this (Finset.sum_nonneg fun j _ => ?_)
  exact Real.sqrt_nonneg _

/-- The group norm on `𝒜`. -/
def affGroupNorm (as : ℝ) (h : AffClosure as) (hn : AffNormLaws as) :
    AddGroupNorm (affSub as h) where
  toFun := fun A => affNorm as A.1
  map_zero' := by
    have := hn.2.1 0 0 h.1
    simpa using this
  add_le' := fun A B => hn.1 A.1 B.1 A.2 B.2
  neg' := fun A => by
    have := hn.2.1 (-1) A.1 A.2
    have e : ((-A : affSub as h) : ℝ → Mat3) = (-1 : ℝ) • A.1 := by simp
    simp only [e, this]; simp
  eq_zero_of_map_eq_zero' := fun A hA => Subtype.ext (hn.2.2 A.1 A.2 hA)

/-- `NormedAddCommGroup` structure on `𝒜`, norm `affNorm as`. -/
@[instance_reducible] def affNAG (as : ℝ) (h : AffClosure as) (hn : AffNormLaws as) :
    NormedAddCommGroup (affSub as h) :=
  (affGroupNorm as h hn).toNormedAddCommGroup

lemma affNAG_norm (as : ℝ) (h : AffClosure as) (hn : AffNormLaws as) (A : affSub as h) :
    @norm _ (affNAG as h hn).toNorm A = affNorm as A.1 := rfl

/-- `NormedSpace ℝ` structure on `𝒜`. -/
def affNS (as : ℝ) (h : AffClosure as) (hn : AffNormLaws as) :
    @NormedSpace ℝ (affSub as h) _ (affNAG as h hn).toSeminormedAddCommGroup := by
  letI := affNAG as h hn
  exact NormedSpace.mk
    (fun c A => by
      have := hn.2.1 c A.1 A.2
      show affNorm as ((c • A : affSub as h) : ℝ → Mat3) ≤ ‖c‖ * affNorm as A.1
      simp only [Submodule.coe_smul]
      rw [this, Real.norm_eq_abs])

/-- Completeness of `𝒜`. -/
theorem affSub_complete (as : ℝ) (h : AffClosure as) (hn : AffNormLaws as)
    (hc : AffCompleteness as) :
    @CompleteSpace (affSub as h) (affNAG as h hn).toUniformSpace := by
  letI := affNAG as h hn
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hu' := Metric.cauchySeq_iff'.1 hu
  obtain ⟨A, hA, hlim⟩ := hc (fun n => (u n).1) (fun n => (u n).2) (by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    refine ⟨N, fun m hm n hn' => ?_⟩
    have := hN m hm n hn'
    rw [dist_eq_norm] at this
    exact this)
  refine ⟨⟨A, hA⟩, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine hlim.congr fun n => ?_
  simp [dist_eq_norm, affNAG_norm]

end UnforcedLeray.Short.PartIIIb.Concrete
