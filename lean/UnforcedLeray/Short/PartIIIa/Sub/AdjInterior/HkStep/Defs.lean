import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared

/-!
# `PartIII-a:T21/2/7/2/1/1/5`: the spatial bootstrap `AdjHkStep` (vocabulary and leaves)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071 (the
weighted energies `E_j` of the reverse-time adjoint and the inequalities
`E_j' + βE_{j+1} ≤ C(E_j + ⋯ + E_0)` in the reverse time: Reynolds cancellation of the transport
term, diffusion-weight errors through the logarithmic derivatives of the weight), 3044-3050 (the
weight), 3052-3058 (the adjoint localized interaction is of order `-1`).

## The route (assembled in `Assembly.lean`)

For a weak adjoint `φ` on `[t, s]` and a closed interval `[a, b] ⊆ [t, s)` (`a = t` allowed: the
reverse evolution ENDS at `t`; the time weight of the energy estimate vanishes near the start `b`
only):
1. `AdjMollEnergy` (the analytic core, SP 3060-3071): if `φ(r)` has level-`k` jets on `[a, b]`
   bounded by `M`, the mollified energies `N_j(r) = cellEnergy c m j (ρ_n ⋆ φ(r))`, `j ≤ k + 1`, are
   continuous on `[a, b]`, differentiable on `(a, b)`, and `-N_j' + βN_{j+1} ≤ C(N_j + M²)` with
   `β > 0`, `C` independent of `n` and `r`;
2. the scalar chain `adjointEnergyChain` (SP 3072-3073, proved) in the reverse time `ζ = b₁ - r`
   with `e₀ = N_k + M²`, `e₁ = N_{k+1}`, `e₂ = N_{k+2}` bounds `N_{k+1}(r)` on `[a, b']`, `b' < b`,
   uniformly in `n`;
3. `CellWeakDerivOfMollBound` (Riesz in `X_{-m,c}`, from `WeightedWeakDerivOfPairing`): uniformly
   bounded mollified derivatives give a periodic weak derivative in `X_{-m,c}`; so `φ(r)` has
   level-`(k+1)` jets on `[a, b']` with a uniform bound (`AdjHkGainOn`, proved in `Assembly.lean`);
4. applied twice, level-`(k+2)` bounds; continuity in `r` of the level-`(k+1)` fields by the
   interpolation inequality `CellInterp` (`‖∂_j f‖² ≤ ‖f‖(2|m|‖∂_jf‖ + ‖∂_j∂_jf‖)`) against the
   level-`k` continuity, with the fields chosen pointwise (`cellWeakD`, `jetExt`) and identified
   through `WeakCellAeUnique` (`Sub/PartIII-a_T21_2_7_2_1_2_1_3_3.lean`).
The general step `adjHkStepOn_of` serves `AdjHkStep` (`I = (t, s)`) and `AdjHkStepEnd`
(`I = [t, s)`, `Sub/PartIII-a_T21_2_7_2_1_2.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Choice of the next fields -/

open Classical in
/-- The chosen periodic weak derivative `∂_j F` in `X_{-m,c}` (`0` if there is none). -/
def cellWeakD (c m : ℝ) (j : Fin 2) (F : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  if h : ∃ G : ℝ × ℝ → ℂ, (∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x) ∧
      MemLp G 2 (B0579.cellMeasure c (-m)) ∧ HasWeakCellDerivC c j F G
  then Classical.choose h else 0

/-- A level-`k` jet `D` extended by the chosen weak derivatives `∂_j (D w)` of its top fields
(`|w| = k`); the fields of length `≤ k` are kept. -/
def jetExt (c m : ℝ) (k : ℕ) (D : List (Fin 2) → ℝ × ℝ → ℂ) : List (Fin 2) → ℝ × ℝ → ℂ
  | [] => D []
  | j :: w => if w.length < k then D (j :: w) else cellWeakD c m j (D w)

theorem cellWeakD_spec {c m : ℝ} {j : Fin 2} {F : ℝ × ℝ → ℂ}
    (h : ∃ G : ℝ × ℝ → ℂ, (∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x) ∧
      MemLp G 2 (B0579.cellMeasure c (-m)) ∧ HasWeakCellDerivC c j F G) :
    (∀ x : ℝ × ℝ, cellWeakD c m j F (x.1 + c, x.2) = cellWeakD c m j F x) ∧
      MemLp (cellWeakD c m j F) 2 (B0579.cellMeasure c (-m)) ∧
      HasWeakCellDerivC c j F (cellWeakD c m j F) := by
  unfold cellWeakD
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem jetExt_of_le (c m : ℝ) (k : ℕ) (D : List (Fin 2) → ℝ × ℝ → ℂ) :
    ∀ w : List (Fin 2), w.length ≤ k → jetExt c m k D w = D w
  | [], _ => rfl
  | j :: w, hw => by
    have hw' : w.length < k := by simpa using hw
    simp only [jetExt, if_pos hw']

theorem jetExt_cons_of_length (c m : ℝ) (k : ℕ) (D : List (Fin 2) → ℝ × ℝ → ℂ) (j : Fin 2)
    {w : List (Fin 2)} (hw : w.length = k) :
    jetExt c m k D (j :: w) = cellWeakD c m j (D w) := by
  simp only [jetExt, if_neg (by omega : ¬ w.length < k)]

/-- A level-`k` jet whose top fields have periodic weak derivatives in `X_{-m,c}` extends by
`jetExt` to a level-`(k + 1)` jet. -/
theorem isCellJet_jetExt {c m : ℝ} {k : ℕ} {f : ℝ × ℝ → ℂ} {D : List (Fin 2) → ℝ × ℝ → ℂ}
    (hD : IsCellJet c m k f D)
    (hex : ∀ w : List (Fin 2), w.length = k → ∀ j : Fin 2, ∃ G : ℝ × ℝ → ℂ,
      (∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x) ∧ MemLp G 2 (B0579.cellMeasure c (-m)) ∧
        HasWeakCellDerivC c j (D w) G) :
    IsCellJet c m (k + 1) f (jetExt c m k D) := by
  have htop : ∀ w : List (Fin 2), w.length = k + 1 →
      (∀ x : ℝ × ℝ, jetExt c m k D w (x.1 + c, x.2) = jetExt c m k D w x) ∧
        MemLp (jetExt c m k D w) 2 (B0579.cellMeasure c (-m)) := by
    intro w hw
    cases w with
    | nil => simp at hw
    | cons j w =>
      have hw' : w.length = k := by simpa using hw
      rw [jetExt_cons_of_length c m k D j hw']
      obtain ⟨h1, h2, -⟩ := cellWeakD_spec (hex w hw' j)
      exact ⟨h1, h2⟩
  refine ⟨hD.base, fun w hw x => ?_, fun w hw => ?_, fun j w hw => ?_⟩
  · rcases Nat.lt_or_ge w.length (k + 1) with h | h
    · rw [jetExt_of_le c m k D w (by omega)]
      exact hD.periodic w (by omega) x
    · exact (htop w (by omega)).1 x
  · rcases Nat.lt_or_ge w.length (k + 1) with h | h
    · rw [jetExt_of_le c m k D w (by omega)]
      exact hD.memX w (by omega)
    · exact (htop w (by omega)).2
  · rw [jetExt_of_le c m k D w (by omega)]
    rcases Nat.lt_or_ge w.length k with h | h
    · rw [jetExt_of_le c m k D (j :: w) (by simpa using h)]
      exact hD.deriv j w h
    · have hwk : w.length = k := by omega
      rw [jetExt_cons_of_length c m k D j hwk]
      exact (cellWeakD_spec (hex w hwk j)).2.2

/-! ## The leaves -/

/-- **Continuity on compact sets gives bounds** (analysis): fields continuous into `X_{-m,c}`
within `I` (as in `AdjHkOn`) are bounded in `X_{-m,c}` on every compact `K ⊆ I`, uniformly over the
finitely many words of length `≤ k` (`wordsLE`, `mem_wordsLE`). Proof: for each word,
`r ↦ (xNorm (D r w)).toReal` is continuous within `I` (`|‖u‖ - ‖v‖| ≤ ‖u - v‖`,
`eLpNorm_sub_le`, finite norms by `memX`), so bounded on `K` (`IsCompact.exists_bound_of_continuousOn`);
take the sum of the bounds over `wordsLE k`. -/
def CompactJetBound : Prop :=
  ∀ (c m : ℝ) (k : ℕ) (I K : Set ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ),
    (∀ r ∈ I, IsCellJet c m k (φ r) (D r)) →
    (∀ w : List (Fin 2), w.length ≤ k → ∀ r ∈ I,
      Tendsto (fun r' => xNorm c (-m) (D r' w - D r w)) (𝓝[I] r) (𝓝 0)) →
    IsCompact K → K ⊆ I → ∃ M : ℝ, ∀ r ∈ K, ∀ w : List (Fin 2), w.length ≤ k →
      xNorm c (-m) (D r w) ≤ ENNReal.ofReal M

/-- **Weak derivative from a bounded pairing, weighted** (Riesz representation in `X_{-m,c}`; the
weighted form of `WeakDerivOfBoundedPairing`, `Sub/T21_2_1/KernelDefs.lean`, proved in
`Sub/T21_2_1/Kernel/WeakDerivRiesz.lean`): if `ψ ↦ ∫_{C_c} f ∂_jψ` converges absolutely and is
bounded by `M ‖ψ‖_{X_{m,c}}` on cylinder tests, then `f` has a weak derivative `∂_j f = g` in
`X_{-m,c}` with `‖g‖_{X_{-m,c}} ≤ 2M`. Proof: as `weakDerivOfBoundedPairing`, with the real Hilbert
space `Lp ℝ 2 (cellMeasure c (-m))` and the embedding `ψ ↦ jb^m ψ` of the tests
(`‖jb^m ψ‖_{X_{-m}} = ‖ψ‖_{X_m}`, `⟪g, jb^m ψ⟫ = ∫_{C_c} g ψ`), `exists_riesz_of_linear` for the
real and the imaginary part. -/
def WeightedWeakDerivOfPairing : Prop :=
  ∀ c m : ℝ, 0 < c → ∀ (f : ℝ × ℝ → ℂ) (j : Fin 2) (M : ℝ≥0∞), M ≠ ⊤ →
    (∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ →
      IntegrableOn (fun x => f x * (B0579.pd j ψ x : ℂ)) (B0579.cell c) ∧
        ‖∫ x in B0579.cell c, f x * (B0579.pd j ψ x : ℂ)‖ₑ ≤
          M * eLpNorm ψ 2 (B0579.cellMeasure c m)) →
    ∃ g : ℝ × ℝ → ℂ, HasWeakCellDerivC c j f g ∧ MemLp g 2 (B0579.cellMeasure c (-m)) ∧
      xNorm c (-m) g ≤ 2 * M

/-- **Weak derivative from uniformly bounded mollified derivatives** (SP 3060-3071: the energy
bound is passed to the limit of the regularization). If `f` is `c`-periodic in `X_{-m,c}` and
`‖∂_j(ρ_n ⋆ f)‖_{X_{-m,c}} ≤ M` for every `n`, then `f` has a periodic weak derivative
`∂_j f = G ∈ X_{-m,c}` with `‖G‖ ≤ 2M`. Proof: for a cylinder test `ψ`,
`∫ f ∂_jψ = lim ∫ (ρ_n ⋆ f) ∂_jψ` (`CellMollTendsto` and the weighted Cauchy-Schwarz bound
`WeightedCS`), `∫ (ρ_n ⋆ f) ∂_jψ = -∫ ∂_j(ρ_n ⋆ f) ψ` (`IbpPdCxWeak`, `CellMollSmooth`), so
`|∫ f ∂_jψ| ≤ M ‖ψ‖_{X_{m,c}}`; then `WeightedWeakDerivOfPairing`, and `G = perRep c g`
(`perRep_eqOn_cell`: same cell integrals and norms). -/
def CellWeakDerivOfMollBound : Prop :=
  ∀ (c m : ℝ) (j : Fin 2) (f : ℝ × ℝ → ℂ) (M : ℝ), 0 < c →
    (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) → MemLp f 2 (B0579.cellMeasure c (-m)) →
    (∀ n : ℕ, xNorm c (-m) (pdCx j (cellMoll n f)) ≤ ENNReal.ofReal M) →
    ∃ G : ℝ × ℝ → ℂ, (∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x) ∧
      MemLp G 2 (B0579.cellMeasure c (-m)) ∧ HasWeakCellDerivC c j f G ∧
      xNorm c (-m) G ≤ ENNReal.ofReal (2 * M)

/-- **The interpolation inequality for smooth periodic fields** (SP 3044-3050: the
diffusion-weight error `|∂_j ⟨x⟩^{-2m}| ≤ 2|m| ⟨x⟩^{-2m}`, `AdjWeightGrad`). For `F` smooth and
`c`-periodic with every partial in `X_{-m,c}`:
`‖∂_jF‖² ≤ ‖F‖ (2|m| ‖∂_jF‖ + ‖∂_j∂_jF‖)` in `X_{-m,c}`. Proof:
`∫_{C_c} ∂_j(jb^{-m} F conj(∂_jF)) = 0` (for `j = 0` the seam terms cancel: `F`, `∂F` are periodic
and `jb(±c/2, x₂)` is one value; for `j = 1` an integrable function with integrable derivative on
each line, `integral_eq_zero_of_hasDerivAt_of_integrable`, Fubini); expand the derivative and use
`AdjWeightGrad` and the weighted Cauchy-Schwarz inequality. -/
def CellInterpSmooth : Prop :=
  ∀ (c m : ℝ) (j : Fin 2) (F : ℝ × ℝ → ℂ), 0 < c → ContDiff ℝ ∞ F →
    (∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x) →
    (∀ w : List (Fin 2), MemLp (adjSpatial w F) 2 (B0579.cellMeasure c (-m))) →
    xNorm c (-m) (pdCx j F) ^ 2 ≤
      xNorm c (-m) F * (ENNReal.ofReal (2 * |m|) * xNorm c (-m) (pdCx j F) +
        xNorm c (-m) (pdCx j (pdCx j F)))

/-- **The interpolation inequality for periodic weak derivatives** (from `CellInterpSmooth` for
`ρ_n ⋆ f`, whose partials are `ρ_n ⋆ g`, `ρ_n ⋆ h` by `CellMollWeakDeriv`, with all partials in
`X_{-m,c}` by `CellMollSmooth`, and the limit `n → ∞` by `CellMollTendsto`): if `g = ∂_j f` and
`h = ∂_j g` weakly, all `c`-periodic in `X_{-m,c}`, then `‖g‖² ≤ ‖f‖ (2|m| ‖g‖ + ‖h‖)`. -/
def CellInterp : Prop :=
  ∀ (c m : ℝ) (j : Fin 2) (f g h : ℝ × ℝ → ℂ), 0 < c →
    (∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) → (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) →
    (∀ x : ℝ × ℝ, h (x.1 + c, x.2) = h x) →
    MemLp f 2 (B0579.cellMeasure c (-m)) → MemLp g 2 (B0579.cellMeasure c (-m)) →
    MemLp h 2 (B0579.cellMeasure c (-m)) →
    HasWeakCellDerivC c j f g → HasWeakCellDerivC c j g h →
    xNorm c (-m) g ^ 2 ≤
      xNorm c (-m) f * (ENNReal.ofReal (2 * |m|) * xNorm c (-m) g + xNorm c (-m) h)

/-- **The energy inequalities of the mollified adjoint** (SP 3060-3071; the analytic core). Let `φ`
be a weak adjoint on `[t, s]` (`IsAdjointWeak`, `AdjTestedDeriv`; `c = ν⁻²`, `ν ≤ 1`, train bounds
`LadTrainBdd` and jets `TrainSTJets`) and `[a, b] ⊆ [t, s)` with `a < b`, on which `φ(r)` has
level-`k` jets `D r` with fields bounded by `M` in `X_{-m,c}`. Then there are `C ≥ 0`, `β > 0`,
independent of the mollification index `n` and of `r`, such that for every `n` and `j ≤ k + 1` the
energy `N_j(r) = cellEnergy c m j (ρ_n ⋆ φ(r))` is continuous on `[a, b]`, differentiable on
`(a, b)`, and `-N_j' + β N_{j+1} ≤ C (N_j + M²)`.

Route. (b) the mollified equation: `(ρ_n ⋆ φ(r))(x) = ∫_{C_c} φ(r) perKer c (ρ_n(x - ·))`
(`CellPeriodize`) is differentiable in `r` by `AdjTestedDeriv` (kernel velocity of the test:
`kerVel`, `Sub/T21_2_1/KernelDefs.lean`), and every `r ↦ ∂^w(ρ_n ⋆ φ(r))` is `C¹` into `X_{-m,c}`
with `∂_r(ρ_n ⋆ φ) = -(νΔ(ρ_n ⋆ φ) + ∇·(ρ_n ⋆ (vφ)) - ρ_n ⋆ χ)`, `χ = K_c^T(φ∇E)`
(`AdjLocalizedCoeff`; tested derivatives continuous in `X` are `X`-derivatives: `LocCylUniq`,
`AdjPairing`, FTC for the Bochner integral); (c) `χ(r) ∈ H^{k+1}_{-m,c}` with norm `≤ C‖φ(r)‖_{H^k}`
(`KTOrderMinusOne`, `B = ∇E(r)`, bounds from `TrainSTJets`); (d) Friedrichs:
`∇·(ρ_n ⋆ (vφ)) = v·∇(ρ_n ⋆ φ) + ∇·[ρ_n⋆, v]φ` with `‖∂^w ∇·[ρ_n⋆, v]φ‖_{X} ≤ C ‖φ‖_{H^{|w|}}`,
`|w| ≤ k`, uniformly in `n` (`|v(y) - v(x)| ≤ ‖∇v‖_∞ |x - y|`, `∫ |∇ρ_n(z)| |z| dz` independent
of `n`, `CellConvBound`); (e) `d/dr ‖∂^w(ρ_n⋆φ)‖² = 2 Re⟨∂^w(ρ_n⋆φ), ∂_r ∂^w(ρ_n⋆φ)⟩`, the diffusion
term integrated by parts on the cell gives `2ν‖∇∂^w(ρ_n⋆φ)‖²` minus the weight error
(`AdjWeightGrad`), one derivative of the transport and compact terms is moved onto the test, and
Young's inequality absorbs `β N_{j+1}`. -/
def AdjMollEnergy (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjTestedDeriv tr t s φ →
      ∀ (k : ℕ) (a b : ℝ), t ≤ a → a < b → b < s →
      ∀ (D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (M : ℝ),
        (∀ r ∈ Icc a b, IsCellJet (ν ^ (-2 : ℝ)) m k (φ r) (D r)) →
        (∀ r ∈ Icc a b, ∀ w : List (Fin 2), w.length ≤ k →
          xNorm (ν ^ (-2 : ℝ)) (-m) (D r w) ≤ ENNReal.ofReal M) →
        ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ ∀ n j : ℕ, j ≤ k + 1 →
          ContinuousOn (fun r => cellEnergy (ν ^ (-2 : ℝ)) m j (cellMoll n (φ r))) (Icc a b) ∧
          ∀ r ∈ Ioo a b, ∃ d : ℝ,
            HasDerivAt (fun r' => cellEnergy (ν ^ (-2 : ℝ)) m j (cellMoll n (φ r'))) d r ∧
            -d + β * cellEnergy (ν ^ (-2 : ℝ)) m (j + 1) (cellMoll n (φ r)) ≤
              C * (cellEnergy (ν ^ (-2 : ℝ)) m j (cellMoll n (φ r)) + M ^ 2)

/-- **One gain of regularity on a closed interval** (SP 3060-3073; proved in `Assembly.lean` from
`AdjMollEnergy`, `adjointEnergyChain`, the mollifier facts and `CellWeakDerivOfMollBound`): if a weak
adjoint has level-`k` jets on `[a, b] ⊆ [t, s)` bounded by `M`, then on `[a, b']`, `b' < b`, every top
field `D r w` (`|w| = k`) has periodic weak derivatives `∂_j (D r w)` in `X_{-m,c}`, bounded uniformly
in `r`. -/
def AdjHkGainOn (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjTestedDeriv tr t s φ →
      ∀ (k : ℕ) (a b : ℝ), t ≤ a → a < b → b < s →
      ∀ (D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (M : ℝ),
        (∀ r ∈ Icc a b, IsCellJet (ν ^ (-2 : ℝ)) m k (φ r) (D r)) →
        (∀ r ∈ Icc a b, ∀ w : List (Fin 2), w.length ≤ k →
          xNorm (ν ^ (-2 : ℝ)) (-m) (D r w) ≤ ENNReal.ofReal M) →
        ∀ b' : ℝ, b' < b → ∃ M' : ℝ, ∀ r ∈ Icc a b', ∀ w : List (Fin 2), w.length = k →
          ∀ j : Fin 2, ∃ G : ℝ × ℝ → ℂ, (∀ x : ℝ × ℝ, G (x.1 + ν ^ (-2 : ℝ), x.2) = G x) ∧
            MemLp G 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
            HasWeakCellDerivC (ν ^ (-2 : ℝ)) j (D r w) G ∧
            xNorm (ν ^ (-2 : ℝ)) (-m) G ≤ ENNReal.ofReal M'

end UnforcedLeray.Short.IIIa
