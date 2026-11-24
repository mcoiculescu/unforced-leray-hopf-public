import UnforcedLeray.Lib.ComplexODEB.Openness
import Mathlib.Topology.MetricSpace.Sequences

/-!
# B0034 helper: continuation in the real wavenumber

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

The mode of B0034 (`paper/main.tex`, lines 1012–1021) is obtained in the cited
source (Lin 2003, Theorem 1.3; Lemma 5.8, Theorem 5.9 and the continuation on
p. 346) by continuation in a real wavenumber `β ∈ (1, α_{max,N})`. This file
proves the topological part of that continuation for the actual Gaussian Evans
function `D(β,c) = evansFunction β a b c` on a log-annulus `[a,b]`:

* the set of unstable wavenumbers is open (`isOpen_unstableWavenumbers`, Hurwitz);
* zeros stay in a fixed disc for `β ≥ 1` (`evansFunction_ne_zero_of_norm_gt`), so a
  sequence of zeros has a convergent subsequence; a limit with `Im c > 0` is again a
  zero by joint continuity;
* hence the unstable set is relatively closed in `(1, α)` as soon as no sequence of
  zeros can converge to a real speed (`NoRealLimitSpeed`), and it is all of
  `(1, α)` as soon as it meets `(1, α)` just below `α` (`BifurcatesBelow`).

`BifurcatesBelow` (Lin's Theorem 5.9) and `NoRealLimitSpeed` (Lin's Lemma 5.8) are
the two analytic inputs of the continuation; they are stated here as explicit
propositions about the actual Evans function and are not assumed anywhere as facts.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology Metric
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans

/-- Nonzero real wavenumbers `β` for which the Rayleigh–Dirichlet problem on `[a,b]`
has an upper-half-plane eigenvalue, i.e. `D(β,c) = 0` for some `Im c > 0`. -/
def unstableWavenumbers (a b : ℝ) : Set ℝ :=
  {β | β ≠ 0 ∧ ∃ c : ℂ, 0 < c.im ∧ evansFunction β a b c = 0}

/-- Local bifurcation input (Lin 2003, Theorem 5.9, at the neutral wavenumber `α`):
every wavenumber slightly below `α` is unstable. -/
def BifurcatesBelow (a b α : ℝ) : Prop :=
  ∃ δ > 0, ∀ β ∈ Ioo (α - δ) α, ∃ c : ℂ, 0 < c.im ∧ evansFunction β a b c = 0

/-- Exclusion of real limiting speeds (Lin 2003, Lemma 5.8): upper-half-plane zeros
`c_k` of `D(β_k,·)` with `β_k → β_s ∈ (1, α)` never converge to a real speed. -/
def NoRealLimitSpeed (a b α : ℝ) : Prop :=
  ∀ (β : ℕ → ℝ) (c : ℕ → ℂ) (βs cs : ℝ), βs ∈ Ioo 1 α →
    Tendsto β atTop (𝓝 βs) → Tendsto c atTop (𝓝 (cs : ℂ)) →
    (∀ k, 0 < (c k).im) → (∀ k, evansFunction (β k) a b (c k) = 0) → False

/-- Relative closedness of the unstable wavenumbers in `(1, α)`. -/
theorem closure_inter_subset_unstable {a b α : ℝ} (hab : a < b)
    (hreal : NoRealLimitSpeed a b α) :
    closure (unstableWavenumbers a b) ∩ Ioo 1 α ⊆ unstableWavenumbers a b := by
  rintro βs ⟨hcl, hβs⟩
  obtain ⟨β, hβmem, hβlim⟩ := mem_closure_iff_seq_limit.mp hcl
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hβlim.eventually (lt_mem_nhds hβs.1))
  set β' : ℕ → ℝ := fun k => β (k + K) with hβ'_def
  have hβ'lim : Tendsto β' atTop (𝓝 βs) := hβlim.comp (tendsto_add_atTop_nat K)
  have hβ'gt : ∀ k, 1 < β' k := fun k => hK _ (Nat.le_add_left K k)
  choose c hcim hcz using fun k => (hβmem (k + K)).2
  obtain ⟨R, hR⟩ := evansFunction_ne_zero_of_norm_gt hab (β₀ := 1) one_pos
  have hcb : ∀ k, c k ∈ closedBall (0 : ℂ) R := fun k => by
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    push Not at h
    exact hR (β' k) (by rw [abs_of_pos (by linarith [hβ'gt k])]; exact (hβ'gt k).le)
      (c k) (hcim k) h (hcz k)
  obtain ⟨cs, -, φ, hφ, hclim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hcb
  have hβφ : Tendsto (β' ∘ φ) atTop (𝓝 βs) := hβ'lim.comp hφ.tendsto_atTop
  have him : 0 ≤ cs.im :=
    ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hclim)
      (Eventually.of_forall fun k => (hcim (φ k)).le)
  rcases him.lt_or_eq with hpos | hzero
  · refine ⟨(lt_trans one_pos hβs.1).ne', cs, hpos, ?_⟩
    have hcont : ContinuousAt (fun p : ℝ × ℂ => evansFunction p.1 a b p.2) (βs, cs) :=
      (continuousOn_evansFunction_parameters a b).continuousAt
        ((isOpen_upperHalfPlane.preimage continuous_snd).mem_nhds hpos)
    have hlim := hcont.tendsto.comp (hβφ.prodMk_nhds hclim)
    have hconst : ((fun p : ℝ × ℂ => evansFunction p.1 a b p.2) ∘
        fun k => ((β' ∘ φ) k, (c ∘ φ) k)) = fun _ => (0 : ℂ) :=
      funext fun k => hcz (φ k)
    rw [hconst] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  · exfalso
    have hcs : cs = ((cs.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
    rw [hcs] at hclim
    exact hreal (β' ∘ φ) (c ∘ φ) βs cs.re hβs hβφ hclim (fun k => hcim (φ k))
      (fun k => hcz (φ k))

/-- Continuation: local bifurcation below `α` and exclusion of real limiting speeds
make every wavenumber in `(1, α)` unstable. -/
theorem Ioo_subset_unstableWavenumbers {a b α : ℝ} (hab : a < b) (hα : 1 < α)
    (hbif : BifurcatesBelow a b α) (hreal : NoRealLimitSpeed a b α) :
    Ioo 1 α ⊆ unstableWavenumbers a b := by
  obtain ⟨δ, hδ, hδ'⟩ := hbif
  refine isPreconnected_Ioo.subset_of_closure_inter_subset (isOpen_unstableWavenumbers hab)
    ?_ (closure_inter_subset_unstable hab hreal)
  set β₁ : ℝ := max (α - δ / 2) ((1 + α) / 2)
  have h1 : 1 < β₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have h2 : β₁ < α := max_lt (by linarith) (by linarith)
  have h3 : α - δ < β₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  exact ⟨β₁, ⟨h1, h2⟩, (lt_trans one_pos h1).ne', hδ' β₁ ⟨h3, h2⟩⟩

/-- Angular index two: if the neutral wavenumber `α` exceeds two, the two analytic
inputs give an upper-half-plane Evans zero at `β = 2`. -/
theorem exists_evans_zero_two_of_continuation {a b α : ℝ} (hab : a < b) (hα : 2 < α)
    (hbif : BifurcatesBelow a b α) (hreal : NoRealLimitSpeed a b α) :
    ∃ c : ℂ, 0 < c.im ∧ evansFunction 2 a b c = 0 :=
  (Ioo_subset_unstableWavenumbers hab (by linarith) hbif hreal ⟨by norm_num, hα⟩).2

end UnforcedLeray.ComplexODEB
