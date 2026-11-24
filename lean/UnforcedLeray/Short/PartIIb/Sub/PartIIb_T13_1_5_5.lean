import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5

/-!
# `PartII-b:T13/1/5/5` decomposition: mollification on the cylinder

Source: `the November 2 reference manuscript` lines 1932-1935 ("interpolation gives
its gradient bound"; the approximation by smooth periodic functions is the standard preliminary).

`CgiMollify` follows from: existence of a mollifier family (`MollExists`), local integrability of
periodic `L^r(cylMeas)` functions (`MollLoc`), smoothness and periodicity of the convolution
(`MollConvNice`), the Young inequality on `cylMeas` (`MollYoung`), the derivative of a convolution
(`MollDeriv`), the weak identity for `D2` pushed through the convolution (`MollWeakD2`), and the
approximate identity in `L^r(cylMeas)` (`MollApprox`).  `cgiMollify_of` is the proved assembly.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- Convolution `(f ⋆ κ)(x) = ∫ f(y) κ(x - y) dy` on the group `Coord = ℝ × (ℝ × ℝ)`. -/
def convK (κ : Coord → ℝ) (f : Coord → ℂ) (x : Coord) : ℂ := ∫ y, f y * (κ (x - y) : ℂ)

/-- A smooth compactly supported kernel. -/
def IsKer (κ : Coord → ℝ) : Prop := ContDiff ℝ ∞ κ ∧ HasCompactSupport κ

/-- A mollifier: smooth, compactly supported, nonnegative, of integral one. -/
def IsMollifier (ρ : Coord → ℝ) : Prop := IsKer ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1

/-- The rescaling `ρ_n(x) = (n+1)^3 ρ((n+1) x)`. -/
def molN (ρ : Coord → ℝ) (n : ℕ) : Coord → ℝ := fun x => ((n : ℝ) + 1) ^ 3 * ρ (((n : ℝ) + 1) • x)

/-- **Mollifier family.** There is a mollifier `ρ` all of whose rescalings `ρ_n` are mollifiers
(`ContDiffBump` on `Coord`, normalized; change of variables `x ↦ (n+1) x` in the integral). -/
def MollExists : Prop := ∃ ρ : Coord → ℝ, IsMollifier ρ ∧ ∀ n : ℕ, IsMollifier (molN ρ n)

/-- **Local integrability.** A `q`-periodic measurable `f` with finite `L^r(cylMeas c)` norm
(`r > 1`, `c > 0`) is locally integrable for Lebesgue measure (cover a compact set by finitely many
`q`-translates of the cell; `qShift` preserves volume; Hölder on a compact set of `s` where
`cylMeas` is Lebesgue times a probability measure on the cell). -/
def MollLoc : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ f : Coord → ℂ, QPeriodicS c f → AEStronglyMeasurable f volume →
    eLpNorm f (ENNReal.ofReal r) (cylMeas c) < ⊤ → LocallyIntegrable f volume

/-- **Convolution is smooth and periodic.** For a locally integrable `q`-periodic `u` and a smooth
compactly supported kernel, `u ⋆ κ` is smooth (differentiation under the integral,
`HasCompactSupport.contDiff_convolution_right`) and exactly `q`-periodic
(translation invariance of the integral). -/
def MollConvNice : Prop :=
  ∀ (c : ℝ) (κ : Coord → ℝ) (u : Coord → ℂ), IsKer κ → QPeriodicS c u →
    LocallyIntegrable u volume →
    ContDiff ℝ ∞ (convK κ u) ∧ ∀ x, convK κ u (qShift c x) = convK κ u x

/-- **Young inequality on `cylMeas`** (Minkowski; `cylMeas c` is Lebesgue in `s`, `η` times the
average over a `q`-period, translation invariant in `s`, `η` and, for periodic `f`, in `q`):
`‖f ⋆ κ‖_{L^r(cylMeas)} ≤ ‖κ‖_{L¹} ‖f‖_{L^r(cylMeas)}` for `q`-periodic `f`. -/
def MollYoung : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ (κ : Coord → ℝ) (f : Coord → ℂ), IsKer κ → QPeriodicS c f →
    AEStronglyMeasurable f volume →
    eLpNorm (convK κ f) (ENNReal.ofReal r) (cylMeas c) ≤
      ENNReal.ofReal (∫ x, |κ x|) * eLpNorm f (ENNReal.ofReal r) (cylMeas c)

/-- **Derivative of a convolution.** For locally integrable `f` and a smooth compactly supported
kernel, `∂_j (f ⋆ κ) = f ⋆ (∂_j κ)` (`j = 0, 1, 2` for `s, q, η`). -/
def MollDeriv : Prop :=
  ∀ (κ : Coord → ℝ) (f : Coord → ℂ), IsKer κ → LocallyIntegrable f volume → ∀ j : Fin 3,
    cdv j (convK κ f) = convK (cpd j κ) f

/-- **Weak identity through the convolution** (SP 1932-1935): if `∫ u ∂_k∂_l φ = ∫ D2 k l φ` for
all space-time tests, then `∂_k∂_l (u ⋆ κ) = D2 k l ⋆ κ` pointwise (apply the weak identity to
the test `y ↦ κ(x - y)`, using `MollDeriv` twice). -/
def MollWeakD2 : Prop :=
  ∀ (κ : Coord → ℝ) (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ), IsKer κ →
    LocallyIntegrable u volume →
    (∀ i j, LocallyIntegrable (D2 i j) volume) →
    (∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
      ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D2 i j x * (φ x : ℂ)) →
    ∀ k l : Fin 2, cdv k.succ (cdv l.succ (convK κ u)) = convK κ (D2 k l)

/-- **Approximate identity in `L^r(cylMeas)`**: for `q`-periodic measurable `f` of finite norm,
`‖f ⋆ ρ_n - f‖ → 0` (continuity of translation in `L^r(cylMeas c)`, plus `MollYoung`). -/
def MollApprox : Prop :=
  ∀ (c r : ℝ), 0 < c → 1 < r → ∀ (ρ : Coord → ℝ), IsMollifier ρ → (∀ n : ℕ, IsMollifier (molN ρ n)) →
    ∀ f : Coord → ℂ, QPeriodicS c f → AEStronglyMeasurable f volume →
    eLpNorm f (ENNReal.ofReal r) (cylMeas c) < ⊤ →
    Tendsto (fun n : ℕ => eLpNorm (fun x => convK (molN ρ n) f x - f x) (ENNReal.ofReal r)
      (cylMeas c)) atTop (𝓝 0)

/-- **Assembly.** `CgiMollify` from the seven leaves. -/
theorem cgiMollify_of (h0 : MollExists) (hL : MollLoc) (hN : MollConvNice) (hY : MollYoung)
    (hD : MollDeriv) (hW : MollWeakD2) (hA : MollApprox) : CgiMollify := by
  intro r hr c hc u D2 hdata
  obtain ⟨hup, hum, hun, hD2, hw⟩ := hdata
  obtain ⟨ρ, hρ, hρn⟩ := h0
  have hlocu : LocallyIntegrable u volume := hL c r hc hr u hup hum hun
  have hlocD : ∀ i j, LocallyIntegrable (D2 i j) volume := fun i j =>
    hL c r hc hr _ (hD2 i j).1 (hD2 i j).2.1 (hD2 i j).2.2
  have hker : ∀ n, IsKer (molN ρ n) := fun n => (hρn n).1
  have hnorm1 : ∀ n, ENNReal.ofReal (∫ x, |molN ρ n x|) = 1 := by
    intro n
    have : ∫ x, |molN ρ n x| = 1 := by
      rw [← (hρn n).2.2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => abs_of_nonneg ((hρn n).2.1 x))
    rw [this]; simp
  have hyoung : ∀ n (f : Coord → ℂ), QPeriodicS c f → AEStronglyMeasurable f volume →
      eLpNorm (convK (molN ρ n) f) (ENNReal.ofReal r) (cylMeas c) ≤
        eLpNorm f (ENNReal.ofReal r) (cylMeas c) := by
    intro n f hf hfm
    simpa [hnorm1 n] using hY c r hc hr (molN ρ n) f (hker n) hf hfm
  refine ⟨fun n => convK (molN ρ n) u, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨hs, hp⟩ := hN c (molN ρ n) u (hker n) hup hlocu
    refine ⟨hs, hp, ?_, ?_, ?_⟩
    · exact lt_of_le_of_lt (hyoung n u hup hum) hun
    · intro i
      have h1 : cdv i.succ (convK (molN ρ n) u) = convK (cpd i.succ (molN ρ n)) u :=
        hD (molN ρ n) u (hker n) hlocu i.succ
      rw [h1]
      have hk : IsKer (cpd i.succ (molN ρ n)) := by
        refine ⟨?_, ?_⟩
        · exact ((hker n).1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
        · exact (hker n).2.fderiv_apply ℝ (cdir i.succ)
      exact lt_of_le_of_lt (hY c r hc hr _ u hk hup hum)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hun)
    · intro k l
      rw [hW (molN ρ n) u D2 (hker n) hlocu hlocD hw k l]
      exact lt_of_le_of_lt (hyoung n _ (hD2 k l).1 (hD2 k l).2.1) (hD2 k l).2.2
  · exact hA c r hc hr ρ hρ hρn u hup hum hun
  · intro k l
    have : ∀ n x, cdv k.succ (cdv l.succ (convK (molN ρ n) u)) x - D2 k l x =
        convK (molN ρ n) (D2 k l) x - D2 k l x := by
      intro n x
      rw [hW (molN ρ n) u D2 (hker n) hlocu hlocD hw k l]
    simp_rw [this]
    exact hA c r hc hr ρ hρ hρn _ (hD2 k l).1 (hD2 k l).2.1 (hD2 k l).2.2

end UnforcedLeray.Short.IIb
