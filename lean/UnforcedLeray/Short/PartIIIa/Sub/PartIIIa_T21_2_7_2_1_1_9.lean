import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/9`: slices of a continuous version (`STRepSliceAe`)

Source: `the November 2 reference manuscript` lines 3060-3061 (the a.e. bookkeeping
of the smooth version of the weak adjoint).  Pure measure theory.

* `PeriodicBoxBound`: a `c`-periodic function dominates its `L²` norm on a box by `xNorm c (-m)`
  (the box is covered by finitely many translates of the cell, `jb` bounded on the strip);
* `AeDense`: an a.e. subset of an open interval is dense in it;
* `AeAllBoxes`: a statement a.e. on every box `[-n, n]²` holds a.e. on the plane;
* `BoxSliceTendsto`: slices of a function continuous on `(t, s) × ℝ²` converge in `L²(box)`.
* `stRepSliceAe_of` assembles them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- The box `[-R, R]²`. -/
def sliceBox (R : ℝ) : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-R) R

/-- **Leaf 1** (periodic box bound; SP 3060-3061): for `c > 0`, `m`, `R` there is a finite `M`
with `‖g‖_{L²(box)} ≤ M ‖g‖_{X_{-m,c}}` for every `c`-periodic `g` that is a.e. strongly measurable
for the cell measure (cover the box by finitely many translates `x₁ + kc` of the cell, on which
the weight `jb^{-m}` is bounded below; periodicity moves each piece to the cell; the periodic
extension of a cell-measurable function is measurable on the plane). The conclusion also gives
measurability of `g` on the box. -/
def PeriodicBoxBound : Prop :=
  ∀ (c m R : ℝ), 0 < c → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
    ∀ g : ℝ × ℝ → ℂ, (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) →
      AEStronglyMeasurable g (B0579.cellMeasure c (-m)) →
      AEStronglyMeasurable g (volume.restrict (sliceBox R)) ∧
        eLpNorm g 2 (volume.restrict (sliceBox R)) ≤ M * xNorm c (-m) g

/-- **Leaf 2**: an a.e. subset of `(t, s)` accumulates at every point of `(t, s)` (a nonempty open
subinterval has positive measure). -/
def AeDense : Prop :=
  ∀ (t s : ℝ) (A : Set ℝ), (∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo t s → r ∈ A) →
    ∀ r₀ ∈ Ioo t s, ∃ᶠ r in 𝓝[Ioo t s] r₀, r ∈ A

/-- **Leaf 3**: a property a.e. on every box `[-n, n]²` holds a.e. on the plane
(`ae_restrict_iUnion_iff`, the boxes exhaust the plane). -/
def AeAllBoxes : Prop :=
  ∀ P : ℝ × ℝ → Prop,
    (∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (sliceBox (n : ℝ))), P x) → ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), P x

/-- **Leaf 4**: `G` continuous on `(t, s) × ℝ²` has slices converging in `L²(K)` on a compact box
(uniform continuity on a compact neighbourhood `[r₀ - δ, r₀ + δ] × K ⊆ (t, s) × ℝ²`). -/
def BoxSliceTendsto : Prop :=
  ∀ (t s : ℝ) (G : ℝ × (ℝ × ℝ) → ℂ), ContinuousOn G (Ioo t s ×ˢ univ) →
    ∀ r₀ ∈ Ioo t s, ∀ R : ℝ,
      Tendsto (fun r => eLpNorm (fun x => G (r, x) - G (r₀, x)) 2 (volume.restrict (sliceBox R)))
        (𝓝[Ioo t s] r₀) (𝓝 0)

/-- `STRepSliceAe` from the four leaves. -/
theorem stRepSliceAe_of (h1 : PeriodicBoxBound) (h2 : AeDense) (h3 : AeAllBoxes)
    (h4 : BoxSliceTendsto) : STRepSliceAe := by
  intro c m t s f F F' hc hts hf hFf hF' hFF' r₀ hr₀
  obtain ⟨D, hD, hDt⟩ := hf
  -- the set of good times
  have hprod : ∀ᵐ p ∂(volume : Measure (ℝ × (ℝ × ℝ))), p ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) →
      F' p = F p := hFF'
  have hae : ∀ᵐ r ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)),
      (r, x) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) → F' (r, x) = F (r, x) :=
    Measure.ae_ae_of_ae_prod hprod
  set A : Set ℝ := {r | ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)),
      (r, x) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) → F' (r, x) = F (r, x)} with hA
  have hdense := h2 t s A (hae.mono fun r hr _ => hr) r₀ hr₀
  have hslice : ∀ r ∈ Ioo t s ∩ A, (fun x => F' (r, x)) =ᵐ[volume] f r := by
    rintro r ⟨hr, hrA⟩
    have : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), F' (r, x) = F (r, x) :=
      (show ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), (r, x) ∈ Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) → F' (r, x) = F (r, x) from hrA).mono fun x hx => hx ⟨hr, mem_univ _⟩
    exact Filter.EventuallyEq.trans (f := fun x => F' (r, x)) (g := fun x => F (r, x)) this (hFf r hr)
  have hcont : ∀ r ∈ Ioo t s, Continuous (fun x : ℝ × ℝ => F' (r, x)) := by
    intro r hr
    refine continuousOn_univ.1 (hF'.comp (Continuous.continuousOn ?_) ?_)
    · exact continuous_const.prodMk continuous_id
    · intro x _; exact ⟨hr, mem_univ _⟩
  have hfmeas : ∀ r ∈ Ioo t s, AEStronglyMeasurable (f r) (B0579.cellMeasure c (-m)) := by
    intro r hr
    have := (hD r hr).memX [] (by simp)
    rw [(hD r hr).base] at this
    exact this.aestronglyMeasurable
  have hfper : ∀ r ∈ Ioo t s, ∀ x : ℝ × ℝ, f r (x.1 + c, x.2) = f r x := by
    intro r hr x
    have := (hD r hr).periodic [] (by simp) x
    rwa [(hD r hr).base] at this
  have hfT : Tendsto (fun r' => xNorm c (-m) (f r' - f r₀)) (𝓝[Ioo t s] r₀) (𝓝 0) := by
    have := hDt [] (by simp) r₀ hr₀
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    rw [(hD r' hr').base, (hD r₀ hr₀).base]
  -- on every box
  refine h3 _ fun n => ?_
  obtain ⟨M, hM, hMb⟩ := h1 c m (n : ℝ) hc
  have hb0 := hMb (f r₀) (hfper r₀ hr₀) (hfmeas r₀ hr₀)
  have hfrT : Tendsto (fun r' => eLpNorm (f r' - f r₀) 2 (volume.restrict (sliceBox (n : ℝ))))
      (𝓝[Ioo t s] r₀) (𝓝 0) := by
    have hM0 : Tendsto (fun r' => M * xNorm c (-m) (f r' - f r₀)) (𝓝[Ioo t s] r₀) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hfT (Or.inr hM)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM0
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact (hMb (f r' - f r₀)
      (fun x => by simp [Pi.sub_apply, hfper r' hr' x, hfper r₀ hr₀ x])
      ((hfmeas r' hr').sub (hfmeas r₀ hr₀))).2
  have hFT := h4 t s F' hF' r₀ hr₀ (n : ℝ)
  have hN : Tendsto (fun r' => eLpNorm (fun x => F' (r', x) - F' (r₀, x)) 2
        (volume.restrict (sliceBox (n : ℝ))) +
      eLpNorm (f r' - f r₀) 2 (volume.restrict (sliceBox (n : ℝ))))
      (𝓝[Ioo t s] r₀) (𝓝 0) := by
    simpa using hFT.add hfrT
  set E := eLpNorm (fun x => F' (r₀, x) - f r₀ x) 2 (volume.restrict (sliceBox (n : ℝ))) with hE
  have hmeasA : AEStronglyMeasurable (fun x => F' (r₀, x) - f r₀ x)
      (volume.restrict (sliceBox (n : ℝ))) :=
    (hcont r₀ hr₀).aestronglyMeasurable.sub hb0.1
  have hE0 : E = 0 := by
    by_contra hne
    have hpos : 0 < E := pos_iff_ne_zero.2 hne
    have hev : ∀ᶠ r in 𝓝[Ioo t s] r₀, _ < E := (tendsto_order.1 hN).2 E hpos
    obtain ⟨r, hrA, hrlt⟩ := (hdense.and_eventually (hev.and self_mem_nhdsWithin)).exists
    obtain ⟨hlt, hrI⟩ := hrlt
    have hsl := hslice r ⟨hrI, hrA⟩
    have hsl' : (fun x => F' (r, x)) =ᵐ[volume.restrict (sliceBox (n : ℝ))] f r :=
      ae_restrict_of_ae hsl
    have hmf : AEStronglyMeasurable (f r - f r₀) (volume.restrict (sliceBox (n : ℝ))) :=
      (hMb (f r - f r₀) (fun x => by simp [Pi.sub_apply, hfper r hrI x, hfper r₀ hr₀ x])
        ((hfmeas r hrI).sub (hfmeas r₀ hr₀))).1
    have hmd : AEStronglyMeasurable (fun x => F' (r, x) - F' (r₀, x))
        (volume.restrict (sliceBox (n : ℝ))) :=
      ((hcont r hrI).aestronglyMeasurable.sub (hcont r₀ hr₀).aestronglyMeasurable)
    have hEq : E = eLpNorm ((f r - f r₀) - (fun x => F' (r, x) - F' (r₀, x))) 2
        (volume.restrict (sliceBox (n : ℝ))) := by
      rw [hE]
      refine eLpNorm_congr_ae ?_
      filter_upwards [hsl'] with x hx
      simp only [Pi.sub_apply]
      rw [← hx]; ring
    have hle : E ≤ eLpNorm (f r - f r₀) 2 (volume.restrict (sliceBox (n : ℝ))) +
        eLpNorm (fun x => F' (r, x) - F' (r₀, x)) 2 (volume.restrict (sliceBox (n : ℝ))) := by
      rw [hEq]
      exact eLpNorm_sub_le hmf hmd (by norm_num)
    exact absurd (lt_of_le_of_lt (hle.trans_eq (add_comm _ _)) hlt) (lt_irrefl _)
  have := (eLpNorm_eq_zero_iff hmeasA (by norm_num)).1 hE0
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx

end UnforcedLeray.Short.IIIa
