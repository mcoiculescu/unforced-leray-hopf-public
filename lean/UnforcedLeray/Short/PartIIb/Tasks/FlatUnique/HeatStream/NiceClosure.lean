import UnforcedLeray.Short.PartIIb.Sub.T11_3

/-!
# Part II-b, leaf `PartII-b:T11/3/1` (`NiceStreamClosure`): nice streams are closed under
`∂_q`, `∂_η`, sums and scalar multiples

Source of record: `the November 2 reference manuscript`, SP 1923-1927 (streams and
planar solenoidal tests). The statement is `NiceStreamClosure` of `Sub/T11_3.lean`.

A nice stream is smooth, `c`-periodic in `q` and vanishing for `|η|` large (`NiceStream`, `Sub/T11.lean`).
The derivatives `∂_q ζ = fderiv ζ · (1,0)` and `∂_η ζ = fderiv ζ · (0,1)` are handled by one
lemma for `p ↦ fderiv ζ p v`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- Periodicity of the derivative: `fderiv ζ (p.1 + c, p.2) = fderiv ζ p` for a `c`-periodic `ζ`.
The translation `x ↦ x + (c, 0)` leaves `ζ` invariant, so its derivative is unchanged. -/
theorem nsc_fderiv_periodic {c : ℝ} {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ) (p : ℝ × ℝ) :
    fderiv ℝ ζ (p.1 + c, p.2) = fderiv ℝ ζ p := by
  have hfun : ζ = fun x => ζ (x + ((c, 0) : ℝ × ℝ)) := by
    funext x
    have hx : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
    show ζ x = ζ (x + ((c, 0) : ℝ × ℝ))
    rw [hx, hζ.periodic x]
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := ζ) ((c, 0) : ℝ × ℝ) (x := p)
  rw [← hfun] at h
  have hx' : (p.1 + c, p.2) = p + ((c, 0) : ℝ × ℝ) := by ext <;> simp
  rw [hx']
  exact h.symm

/-- Far from the support, the derivative vanishes: if `ζ = 0` on `{|η| ≥ L}` then
`fderiv ζ p = 0` whenever `|p.2| ≥ L + 1`, since `ζ` vanishes on the open neighbourhood
`{|η| > L}` of `p`. -/
theorem nsc_fderiv_far_zero {L : ℝ} {ζ : ℝ × ℝ → ℝ}
    (hL : ∀ p : ℝ × ℝ, L ≤ |p.2| → ζ p = 0) (p : ℝ × ℝ) (hp : L + 1 ≤ |p.2|) :
    fderiv ℝ ζ p = 0 := by
  have hopen : IsOpen {y : ℝ × ℝ | L < |y.2|} :=
    isOpen_lt continuous_const continuous_snd.abs
  have hmem : p ∈ {y : ℝ × ℝ | L < |y.2|} := by
    show L < |p.2|
    linarith
  have hev : ζ =ᶠ[𝓝 p] (0 : ℝ × ℝ → ℝ) :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem)
      (fun y hy => hL y (le_of_lt (show L < |y.2| from hy)))
  rw [hev.fderiv_eq]
  simp

/-- For a nice stream `ζ` and a fixed direction `v`, the directional derivative
`p ↦ fderiv ζ p v` is again a nice stream. -/
theorem nsc_fderiv_apply {c : ℝ} {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ) (v : ℝ × ℝ) :
    NiceStream c (fun p => fderiv ℝ ζ p v) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (contDiff_infty_iff_fderiv.mp hζ.smooth).2.clm_apply contDiff_const
  · intro p
    show fderiv ℝ ζ (p.1 + c, p.2) v = fderiv ℝ ζ p v
    rw [nsc_fderiv_periodic hζ p]
  · obtain ⟨L, hL⟩ := hζ.compact
    refine ⟨L + 1, fun p hp => ?_⟩
    show fderiv ℝ ζ p v = 0
    rw [nsc_fderiv_far_zero hL p hp]
    simp

/-- Sums of nice streams are nice. -/
theorem nsc_add {c : ℝ} {ζ ξ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ) (hξ : NiceStream c ξ) :
    NiceStream c (ζ + ξ) := by
  obtain ⟨L₁, h₁⟩ := hζ.compact
  obtain ⟨L₂, h₂⟩ := hξ.compact
  refine ⟨hζ.smooth.add hξ.smooth, ?_, ⟨max L₁ L₂, fun p hp => ?_⟩⟩
  · intro p
    show ζ (p.1 + c, p.2) + ξ (p.1 + c, p.2) = ζ p + ξ p
    rw [hζ.periodic p, hξ.periodic p]
  · show ζ p + ξ p = 0
    rw [h₁ p (le_trans (le_max_left _ _) hp), h₂ p (le_trans (le_max_right _ _) hp), add_zero]

/-- Scalar multiples of nice streams are nice. -/
theorem nsc_smul {c : ℝ} {ζ : ℝ × ℝ → ℝ} (a : ℝ) (hζ : NiceStream c ζ) :
    NiceStream c (fun p => a * ζ p) := by
  obtain ⟨L, h⟩ := hζ.compact
  refine ⟨contDiff_const.mul hζ.smooth, ?_, ⟨L, fun p hp => ?_⟩⟩
  · intro p
    show a * ζ (p.1 + c, p.2) = a * ζ p
    rw [hζ.periodic p]
  · show a * ζ p = 0
    rw [h p hp, mul_zero]

/-- **Leaf `PartII-b:T11/3/1`**: nice streams are closed under `∂_q`, `∂_η`, sums and scalar
multiples. -/
theorem niceStreamClosure : NiceStreamClosure := by
  unfold NiceStreamClosure
  intro c ζ ξ a hζ hξ
  exact ⟨nsc_fderiv_apply hζ (1, 0), nsc_fderiv_apply hζ (0, 1), nsc_add hζ hξ, nsc_smul a hζ⟩

end UnforcedLeray.Short.IIb
