import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18`: the energy core `AdjMollEnergy` (vocabulary and leaves)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3071
(energies `E_j`, Reynolds cancellation of the transport term, diffusion-weight errors), 3044-3050
(the weight and its logarithmic derivatives, `AdjWeightGrad`), 3052-3058 (the adjoint localized
interaction is of order `-1`).

## Route

For a weak adjoint `φ` on `[t, s]` the mollified slices `G_n(r) = ρ_n ⋆ φ(r)` are smooth, periodic,
with all partials in `X_{-m,c}`, and satisfy (SP 3060, `-∂_rφ = νΔφ + ∇·(vφ) - χ`,
`χ = K_c^T(φ∇E)`)
`∂_r G_n = mollRate ν v(r) n φ(r) χ(r)`, `mollRate = -(νΔG_n + ∇·(ρ_n ⋆ (vφ)) - ρ_n ⋆ χ)`.

* `MollRateDeriv` (dynamics, leaf `/1`): `N_j(r) = cellEnergy c m j G_n(r)` is continuous on `[a, b]`
  and differentiable on `(a, b)` with derivative `energyRate c m j G_n (mollRate …)`
  `= Σ_{|w| ≤ j} 2 Re ⟨∂^w G_n, ∂^w ∂_r G_n⟩`, for any `χ(r)` that represents `K_c^T(φ(r)∇E(r))`
  through the pairing identity; the existence of such a `χ` with jet bounds is `KTOrderMinusOneUnif`;
* `StaticMollEnergy` (statics, leaf `/2`): at one age, the energy rate satisfies
  `-energyRate + β N_{j+1} ≤ C (N_j + M²)`, uniformly in `n`, from the level-`k` bound `M` of `φ`,
  the level-`(k+1)` bound `C_χ M` of `χ` and the derivative bounds of the slice `v(r)`;
* the train bridges `TrainSliceVel`, `TrainGradBdd` (leaves `/3`, `/4`) turn `TrainSTJets` into the
  slice data used above;
* `adjMollEnergy_of` (`Assembly.lean`): `AdjMollEnergy` from the five leaves.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The real part of the `X_{-m,c}` inner product `⟨f, g⟩ = ∫_{C_c} f ḡ jb^{-m}`. -/
def ipX (c m : ℝ) (f g : ℝ × ℝ → ℂ) : ℝ :=
  (∫ x, f x * (starRingEnd ℂ) (g x) ∂(B0579.cellMeasure c (-m))).re

/-- The time derivative of the energy `cellEnergy c m j G` along a path `G(r)` with
`∂_r G = dG`: `Σ_{|w| ≤ j} 2 Re ⟨∂^w G, ∂^w dG⟩`. -/
def energyRate (c m : ℝ) (j : ℕ) (G dG : ℝ × ℝ → ℂ) : ℝ :=
  ∑ w ∈ wordsLE j, 2 * ipX c m (adjSpatial w G) (adjSpatial w dG)

/-- The age derivative of the mollified adjoint (SP 3060, `-∂_rφ = νΔφ + ∇·(vφ) - χ`):
`∂_r(ρ_n ⋆ φ) = -(νΔ(ρ_n ⋆ φ) + ∇·(ρ_n ⋆ (vφ)) - ρ_n ⋆ χ)`, where
`∇·(ρ_n ⋆ (vφ)) = Σ_l (∂_lρ_n) ⋆ (v_l φ)`. -/
def mollRate (ν : ℝ) (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (n : ℕ) (φ χ : ℝ × ℝ → ℂ) :
    ℝ × ℝ → ℂ := fun x =>
  -((ν : ℂ) * (adjSpatial [0, 0] (cellMoll n φ) x + adjSpatial [1, 1] (cellMoll n φ) x) +
    ∑ l : Fin 2, cellConv (B0579.pd l (molKer n)) (fun y => ((v y l : ℝ) : ℂ) * φ y) x -
    cellMoll n χ x)

/-- A slice `v` of the train: smooth, `c`-periodic, divergence free, with the `i`-th derivative
bounded by `Av i` (SP 270-288, 2866-2870). -/
def SliceVel (c : ℝ) (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (Av : ℕ → ℝ) : Prop :=
  ContDiff ℝ ∞ v ∧ UnforcedLeray.Cyl.IsPeriodic c v ∧
    (∀ z, UnforcedLeray.Cyl.divergence v z = 0) ∧
    ∀ (i : ℕ) (x : ℝ × ℝ), ‖iteratedFDeriv ℝ i v x‖ ≤ Av i

/-! ## The leaves -/

/-- **(Leaf `/1`) The mollified energies are differentiable in the age** (SP 3060-3071: the energies
are classical quantities of the reverse time; the weak solution is regularized in `x`).
For a weak adjoint `φ` on `[t, s]` (`IsAdjointWeak`, `AdjTestedDeriv`, `LadTrainBdd` on every
`[0, S]`), `[a, b] ⊆ [t, s)`, and any family `χ(r)`, `r ∈ [a, b]`, of periodic fields of `X_{-m,c}`
representing `K_c^T(φ(r)∇E(r))` through the pairing identity of `AdjLocalizedCoeff`: for every `n`
and `j`, `N_j(r) = cellEnergy c m j (ρ_n ⋆ φ(r))` is continuous on `[a, b]` and has the derivative
`energyRate c m j (ρ_n ⋆ φ(r)) (mollRate ν v(r) n φ(r) χ(r))` at every `r ∈ (a, b)`.

Route. (b) pointwise: `(ρ_n ⋆ φ(r))(x) = ∫_{C_c} φ(r) perKer c (ρ_n(x - ·))` (`CellPeriodize`), and the
test `perKer c (ρ_n(x - ·))` has a kernel velocity (`kerVel`, `Sub/T21_2_1/KernelDefs.lean`), so
`AdjTestedDeriv` gives `∂_r(ρ_n ⋆ φ)(x)` as `-∫ φ(r) A ψ_x`; integrating by parts (`CellPeriodize`:
`∂_j perKer = perKer ∂_j`) this is `mollRate ν v(r) n φ(r) χ(r) (x)`, `χ` through the pairing identity;
(b') every `r ↦ ∂^w(ρ_n ⋆ φ(r))` has the `X`-derivative `∂^w mollRate …` on `(a, b)`: the candidate
derivative is continuous into `X` (`AdjLocalizedCoeff`: `K r w` continuous, `χ(r) = K r (φ r)` a.e. by
`LocCylUniq`, `AdjPairing`; `CellConvBound`; `IsAdjointWeak.strongCont`), tested derivatives that are
`X`-continuous are `X`-derivatives (`XDerivOfTested`, `Sub/AdjInterior/TimeJets/Defs.lean`; shared with
`PartIII-a:T21/2/7/2/1/1/6/org`); (b'') the derivative of `‖F(r)‖²_X` is `2 Re ⟨F, F'⟩` for an
`X`-differentiable path, summed over the words. Continuity on `[a, b]` from `strongCont` and
`CellConvBound`, `CellConvDeriv`. -/
def MollRateDeriv (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjTestedDeriv tr t s φ →
      ∀ (a b : ℝ), t ≤ a → a < b → b < s → ∀ χ : ℝ → ℝ × ℝ → ℂ,
        (∀ r ∈ Icc a b, (∀ x : ℝ × ℝ, χ r (x.1 + ν ^ (-2 : ℝ), x.2) = χ r x) ∧
          MemLp (χ r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) ∧
          ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
            IsKernelBiotSavart (ν ^ (-2 : ℝ)) ψ uψ →
            IntegrableOn (fun x => φ r x *
                ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
                  uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ))
              (B0579.cell (ν ^ (-2 : ℝ))) ∧
            ∫ x in B0579.cell (ν ^ (-2 : ℝ)), χ r x * (ψ x : ℂ) =
              ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r x *
                ((uψ x 0 * B0579.pd 0 (UnforcedLeray.B0238.Ec tr r) x +
                  uψ x 1 * B0579.pd 1 (UnforcedLeray.B0238.Ec tr r) x : ℝ) : ℂ)) →
        ∀ n j : ℕ,
          ContinuousOn (fun r => cellEnergy (ν ^ (-2 : ℝ)) m j (cellMoll n (φ r))) (Icc a b) ∧
          ∀ r ∈ Ioo a b,
            HasDerivAt (fun r' => cellEnergy (ν ^ (-2 : ℝ)) m j (cellMoll n (φ r')))
              (energyRate (ν ^ (-2 : ℝ)) m j (cellMoll n (φ r))
                (mollRate ν (tr.v r) n (φ r) (χ r))) r

/-- **(Leaf `/2`) The static energy inequality of the mollified adjoint** (SP 3060-3071; the
pointwise-in-age algebra).  For `ν ≤ 1`, `c = ν⁻²`, level `k`, derivative bounds `Av` of the slice
velocity and the order `-1` constant `Cχ`: there are `C ≥ 0`, `β > 0` such that for every slice `v`
with `SliceVel c v Av`, every `φ` with a level-`k` jet `D` bounded by `M` in `X_{-m,c}`, every `χ`
with a level-`(k+1)` jet `Dχ` bounded by `Cχ M`, every `n` and `j ≤ k + 1`,
`-energyRate c m j G (mollRate ν v n φ χ) + β N_{j+1}(G) ≤ C (N_j(G) + M²)`, `G = ρ_n ⋆ φ`.

Route (`G = ρ_n ⋆ φ`, `∂^w G = ρ_n ⋆ D w` for `|w| ≤ k`, `adjSpatial_cellMoll_jet`): (d) Friedrichs:
`∇·(ρ_n ⋆ (vφ)) = v·∇G + R_n`, `R_n(x) = ∫ ∇ρ_n(x - y)·(v(y) - v(x)) φ(y) dy`, and for `|w| ≤ k`
`‖∂^w R_n‖_X ≤ C Σ_{|w'| ≤ |w|} ‖D w'‖_X` uniformly in `n` (`|v(y) - v(x)| ≤ ‖∇v‖_∞ |x - y|`,
`∫ |∇ρ_n(z)||z| dz` independent of `n`, `CellShiftBound`, `CellConvBound`, Leibniz with the derivative
bounds of `v`); (e) weighted integrations by parts on the cell for the smooth periodic fields
`∂^wG` (`CellInterpSmooth`'s computation): `Re⟨F, νΔF⟩ = -ν‖∇F‖² + (weight error)` with the weight error
bounded by `2|m|ν‖F‖‖∇F‖` (`AdjWeightGrad`), and `Re⟨F, v·∇F⟩ = -½∫ (v·∇jb^{-m})|F|²` (`div v = 0`)
bounded by `C‖F‖²` (`AdjWeightGrad`); commutators `[∂^w, v·∇]` have order `|w|` and are bounded by
Leibniz; (f) the algebra: `2ν‖∇∂^wG‖²` summed over `|w| ≤ j` dominates `2ν (N_{j+1} - N_0)`-type
terms (each word of length `1..j+1` is `l :: w'` once), the term `⟨∂^wG, ∂^w(ρ_n ⋆ χ)⟩` is bounded by
`N_j^{1/2} Cχ M` (`CellMollBound`), for `|w| = k+1` one derivative of the `R_n` term is moved onto
`∂^wG` (`‖∂^{w'}R_n‖ ≤ C M`, `|w'| = k`) and Young's inequality absorbs it into `β N_{j+1}`. -/
def StaticMollEnergy (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ (k : ℕ) (Av : ℕ → ℝ) (Cχ : ℝ),
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧
      ∀ (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)), SliceVel (ν ^ (-2 : ℝ)) v Av →
        ∀ (φ χ : ℝ × ℝ → ℂ) (D Dχ : List (Fin 2) → ℝ × ℝ → ℂ) (M : ℝ),
          IsCellJet (ν ^ (-2 : ℝ)) m k φ D →
          (∀ w : List (Fin 2), w.length ≤ k →
            xNorm (ν ^ (-2 : ℝ)) (-m) (D w) ≤ ENNReal.ofReal M) →
          IsCellJet (ν ^ (-2 : ℝ)) m (k + 1) χ Dχ →
          (∀ w : List (Fin 2), w.length ≤ k + 1 →
            xNorm (ν ^ (-2 : ℝ)) (-m) (Dχ w) ≤ ENNReal.ofReal (Cχ * M)) →
          ∀ n j : ℕ, j ≤ k + 1 →
            -energyRate (ν ^ (-2 : ℝ)) m j (cellMoll n φ) (mollRate ν v n φ χ) +
                β * cellEnergy (ν ^ (-2 : ℝ)) m (j + 1) (cellMoll n φ) ≤
              C * (cellEnergy (ν ^ (-2 : ℝ)) m j (cellMoll n φ) + M ^ 2)

/-- **(Leaf `/3`) The slices of the train velocity** (SP 270-288, 2866-2870): from `TrainSTJets`
(joint derivatives of `v` bounded on `[0, S] × ℝ²`, within `[0, ∞) × ℝ²`) every slice `v(r)`,
`r ∈ [0, S]`, is smooth, `c`-periodic (`IsTrain.periodic_v`), divergence free (`IsTrain.solenoidal`),
and its `i`-th spatial derivative is bounded by the joint derivative bound `Av i` independent of `r`
(`iteratedFDeriv` of the slice is `iteratedFDerivWithin` of the space-time field composed with the
inclusion `x ↦ (r, x)`; for `r = 0` the one-sided derivative within `Ici 0 ×ˢ univ`). -/
def TrainSliceVel : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (m S : ℝ), 0 ≤ S → TrainSTJets tr m S →
    ∃ Av : ℕ → ℝ, ∀ r ∈ Icc (0 : ℝ) S, SliceVel c (tr.v r) Av

/-- **(Leaf `/4`) The vorticity gradient satisfies the coefficient hypotheses of
`KTOrderMinusOneUnif`** (SP 3052-3058): from `TrainSTJets`, for each `i` there is `A` with, for every
`r ∈ [0, S]` and `l`, `B_l = ∂_l E(r)` smooth, `c`-periodic and
`(1 + x₂²)^{(m+1)/2} ‖D^{i'} B_l(x)‖ ≤ A` for `i' ≤ i` (`B_l = fderiv E ∘ dir l`, so
`‖D^{i'}B_l(x)‖ ≤ ‖D^{i'+1}E(x)‖`, the slice derivative bounded by the joint derivative bound of
`TrainSTJets` with `n = i'`; smoothness and periodicity from `IsTrain.smooth_v`, `periodic_v`
through `Cyl.curl`). -/
def TrainGradBdd : Prop :=
  ∀ (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (m S : ℝ), 0 ≤ S → TrainSTJets tr m S →
    ∀ i : ℕ, ∃ A : ℝ, ∀ r ∈ Icc (0 : ℝ) S,
      (∀ l : Fin 2, ContDiff ℝ ∞ (B0579.pd l (UnforcedLeray.B0238.Ec tr r))) ∧
      (∀ (l : Fin 2) (x : ℝ × ℝ), B0579.pd l (UnforcedLeray.B0238.Ec tr r) (x.1 + c, x.2) =
        B0579.pd l (UnforcedLeray.B0238.Ec tr r) x) ∧
      ∀ (l : Fin 2) (i' : ℕ), i' ≤ i → ∀ x : ℝ × ℝ,
        (1 + x.2 ^ 2) ^ ((m + 1) / 2) *
          ‖iteratedFDeriv ℝ i' (B0579.pd l (UnforcedLeray.B0238.Ec tr r)) x‖ ≤ A

/-- **(Leaf `/5`) The order `-1` bound with a constant independent of the coefficient**: the
statement of `KTOrderMinusOne` (`Shared.lean`) with `C` chosen before `B` (it depends only on
`c, m, j, A`: the near/far split of SP 3052-3058 uses only the weighted bounds of `D^iB`, `i ≤ j`).
Needed because `B = ∇E(r)` varies with the age `r` and the energy constants must be uniform in `r`. -/
def KTOrderMinusOneUnif (m : ℝ) : Prop :=
  1 < m → ∀ c : ℝ, 1 ≤ c → ∀ (j : ℕ) (A : ℝ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ B : Fin 2 → ℝ × ℝ → ℝ, (∀ l, ContDiff ℝ ∞ (B l)) →
    (∀ l (x : ℝ × ℝ), B l (x.1 + c, x.2) = B l x) →
    (∀ l (i : ℕ), i ≤ j → ∀ x : ℝ × ℝ,
      (1 + x.2 ^ 2) ^ ((m + 1) / 2) * ‖iteratedFDeriv ℝ i (B l) x‖ ≤ A) →
    ∀ (f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ), IsCellJet c m j f D →
      ∃ (χ : ℝ × ℝ → ℂ) (Dχ : List (Fin 2) → ℝ × ℝ → ℂ), IsCellJet c m (j + 1) χ Dχ ∧
        (∀ w : List (Fin 2), w.length ≤ j + 1 →
          xNorm c (-m) (Dχ w) ≤ ENNReal.ofReal C * jetNorm c m j D) ∧
        ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest c ψ →
          IsKernelBiotSavart c ψ uψ →
          IntegrableOn (fun x => f x * ((uψ x 0 * B 0 x + uψ x 1 * B 1 x : ℝ) : ℂ))
              (B0579.cell c) ∧
            ∫ x in B0579.cell c, χ x * (ψ x : ℂ) =
              ∫ x in B0579.cell c, f x * ((uψ x 0 * B 0 x + uψ x 1 * B 1 x : ℝ) : ℂ)

theorem ktOrderMinusOne_of_unif (m : ℝ) (h : KTOrderMinusOneUnif m) : KTOrderMinusOne m :=
  fun hm c hc j B A hB hBp hBb => by
    obtain ⟨C, hC0, hC⟩ := h hm c hc j A
    exact ⟨C, hC0, fun f D hD => hC B hB hBp hBb f D hD⟩

end UnforcedLeray.Short.IIIa
