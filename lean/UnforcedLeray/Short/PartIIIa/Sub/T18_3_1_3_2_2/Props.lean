import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2_2.Defs
import UnforcedLeray.Infra.JointMeasurableRep

/-!
# Part III-a, `PartIII-a:T18/3/1/3/2/2/org`: the leaf statements of `LMDerivRepAEH1`

Source of record: `the November 2 reference manuscript` (SP) lines 3427-3440 and
3541-3552; objects and overview in `Sub/T18_3_1_3_2_2/Defs.lean`. Each `def` below is the statement

-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## The pairing -/

/-- **Continuity of the pairing in the second slot** (Cauchy-Schwarz on `L²(cell; ℂ²)`). -/
def LMIpTendstoRight : Prop :=
  ∀ (c : ℝ) (f g₀ : LMSpField) (g : ℕ → LMSpField), LMCellL2 c f → LMCellL2 c g₀ →
    (∀ n, LMCellL2 c (g n)) →
    Tendsto (fun n : ℕ => ∫ x in B0579.cell c, ∑ i : Fin 2, ‖g n x i - g₀ x i‖ ^ 2) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => LMIp c f (g n)) atTop (𝓝 (LMIp c f g₀))

/-- **Integration by parts on the cell for smooth periodic `H¹` scalars** (SP 3541-3552, the pairing
`⟨Δu_k, u_k⟩ = -‖∇u_k‖²`; no compact support in `η`). -/
def LMSmoothIBP : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (j : Fin 2) (a b : ℝ × ℝ → ℂ), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
    (∀ x : ℝ × ℝ, a (x.1 + c, x.2) = a x) → (∀ x : ℝ × ℝ, b (x.1 + c, x.2) = b x) →
    MemLp a 2 (volume.restrict (B0579.cell c)) → MemLp b 2 (volume.restrict (B0579.cell c)) →
    MemLp (LMPd j a) 2 (volume.restrict (B0579.cell c)) →
    MemLp (LMPd j b) 2 (volume.restrict (B0579.cell c)) →
    ∫ x in B0579.cell c, starRingEnd ℂ (a x) * LMPd j b x =
      -∫ x in B0579.cell c, starRingEnd ℂ (LMPd j a x) * b x

/-- **`∂ⱼ J_k` is anti-self-adjoint on `L²(cell; ℂ²)`** (SP 3541-3552, the pairing
`⟨J_k 𝒫₀ div F, u_k⟩ = -⟨F, ∇J_k² b⟩`). -/
def LMAntiSymm : Prop :=
  ∀ c : ℝ, 0 < c → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J → LMMollH1 c J →
    ∀ (k : ℕ) (j : Fin 2) (f g : LMSpField), LMCellL2 c f → LMCellL2 c g →
      LMIp c f (fun x i => LMPd j (fun y => J k g y i) x) =
        -LMIp c (fun x i => LMPd j (fun y => J k f y i) x) g

/-! ## The Leray projection on `ℂ²`-valued fields -/

/-- **`𝒫₀` is self-adjoint on `L²(cell; ℂ²)`** (`Cyl.inner_P0_comm`; SP 3427-3440). -/
def LMP0CAdj : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f g : LMSpField, LMCellL2 c f → LMCellL2 c g →
    LMIp c (P0C c f) g = LMIp c f (P0C c g)

/-- **`𝒫₀ g = g` for weakly divergence-free `g`** (`Cyl.P0_eq_self`; SP 3427-3440). -/
def LMP0CFix : Prop :=
  ∀ c : ℝ, 0 < c → ∀ g : LMSpField, LMCellL2 c g → LMWeakDivFree c g →
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2, P0C c g x i = g x i

/-- **`𝒫₀` is an `L²` contraction** (`Cyl.norm_P0_le`; SP 3427-3440). -/
def LMP0CContr : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : LMSpField, LMCellL2 c f →
    ∫ x in B0579.cell c, ∑ i : Fin 2, ‖P0C c f x i‖ ^ 2 ≤
      ∫ x in B0579.cell c, ∑ i : Fin 2, ‖f x i‖ ^ 2

/-! ## The mollified test -/

/-- **`J_k f` is weakly divergence free when `f` is** (`divFreeWeak`, and integration by parts for the
smooth periodic `H¹` field `J_k f`, `LMSmoothWeakPd`; SP 3427-3440). -/
def LMJWeakDiv : Prop :=
  ∀ c : ℝ, 0 < c → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J → LMMollH1 c J →
    ∀ (k : ℕ) (f : LMSpField), LMCellL2 c f → LMWeakDivFree c f → LMWeakDivFree c (J k f)

/-- **The real and imaginary parts of `J_k f` are `H¹` divergence-free tests** when `f` is weakly
divergence free (SP 3427-3440, test `J_k φ₀`). -/
def LMH1Test : Prop :=
  ∀ c : ℝ, 0 < c → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J → LMMollH1 c J →
    ∀ (k : ℕ) (f : LMSpField), LMCellL2 c f → LMWeakDivFree c f →
      IsH1DivFreeTest c (fun x i => (J k f x i).re) ∧ IsH1DivFreeTest c (fun x i => (J k f x i).im)

/-- **The tested equation for a complexified test, slicewise in `s`** (SP 3427-3440): `ExtWeakH1`
for `Re w`, `Im w`, with Fubini on `(0,∞) × cell`; the inner integral splits on good slices. -/
def LMSliceTested : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ExtWeakH1 c ν μ F b G →
    ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioi (0 : ℝ) →
    ∀ w : LMSpField, IsH1DivFreeTest c (fun x i => (w x i).re) →
      IsH1DivFreeTest c (fun x i => (w x i).im) →
      ∫ s in Ioi (0 : ℝ),
        (-(((deriv ψ s : ℝ) : ℂ) * LMIp c w (fun y => b (s, y))) +
          ((ψ s : ℝ) : ℂ) * ((μ / (s : ℂ)) * LMIp c w (fun y => b (s, y))) +
          ((ψ s : ℝ) : ℂ) * ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in B0579.cell c,
            starRingEnd ℂ (LMPd j (fun y => w y i) x) * lmTens ν F G (s, x) i j) = 0

/-! ## Joint measurability -/

/-- **`s ↦ Z(s)` has a jointly measurable version** (`IsLMMollifier.measurable`, difference
quotients in `x`; on a slice where all columns of `T` are `L²` the field `J_k T_{·j}` is smooth).
SP 3427-3440. -/
def LMDivJMeasRep : Prop :=
  ∀ c : ℝ, 0 < c → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J → ∀ (k : ℕ)
    (T : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ), (∀ i j, Measurable fun p => T p i j) →
    ∃ Y : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => Y p i) ∧
      ∀ s : ℝ, (∀ j : Fin 2, LMCellL2 c (fun y i => T (s, y) i j)) →
        ∀ (x : ℝ × ℝ) (i : Fin 2), Y (s, x) i = lmDivJ J k (fun y => T (s, y)) x i

/-- **A jointly measurable field is a strongly measurable path in `L²(cell; ℝ²)`** (pure measure
theory; `toL2v` is `0` on the slices outside `L²`). -/
def LMToL2vPath : Prop :=
  ∀ c : ℝ, 0 < c → ∀ f : ℝ × (ℝ × ℝ) → UnforcedLeray.Cyl.Vec2, Measurable f →
    StronglyMeasurable (fun s : ℝ => toL2v c (fun x => f (s, x)))

/-- **`s ↦ 𝒫₀ Y(s)` has a jointly measurable version** (`LMToL2vPath`, `Cyl.P0` continuous,
`Infra.JointMeasurableRep.exists_stronglyMeasurable_rep`). SP 3427-3440. -/
def LMP0Rep : Prop :=
  ∀ c : ℝ, 0 < c → ∀ Y : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => Y p i) →
    ∃ Yt : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => Yt p i) ∧
      ∀ s : ℝ, ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
        Yt (s, x) i = P0C c (fun y => Y (s, y)) x i

/-! ## Local `L²` bounds and integrability in `s` -/

/-- **`u_k = J_k b ∈ L²_loc((0,∞); L²(cell))`** (`IsLMMollifier.contr` on good slices, Tonelli,
`energyLoc`). SP 3427-3440. -/
def LMUkL2Loc : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J →
    ∀ (k : ℕ) (s₁ s₂ : ℝ), 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
        ENNReal.ofReal (vnorm2 (fun i => LMMollU J b k p.1 p.2 i) ^ 2) < ⊤

/-- **`𝒫₀ Z ∈ L²_loc((0,∞); L²(cell))`** (`LMP0CContr`, `gradL2`, Tonelli, `energyLoc`, `l2loc`).
SP 3427-3440. -/
def LMYtL2Loc : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J → LMMollH1 c J →
    ∀ (k : ℕ) (Yt : ℝ × (ℝ × ℝ) → Fin 2 → ℂ), (∀ i, Measurable fun p => Yt p i) →
    (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      Yt (s, x) i = P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y))) x i) →
    ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => Yt p i) ^ 2) < ⊤

/-- **`u' = -(μ/s) u + Y ∈ L²_loc((0,∞); L²(cell))`** when `u, Y` are (`|μ/s| ≤ |μ|/s₁` on
`[s₁, s₂]`; `|a + b|² ≤ 2|a|² + 2|b|²`). -/
def LMUDerL2Loc : Prop :=
  ∀ (c : ℝ) (μ : ℂ) (u : ℝ → LMSpField) (Y : ℝ × (ℝ × ℝ) → Fin 2 → ℂ),
    (∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i) → (∀ i, Measurable fun p => Y p i) →
    ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) < ⊤ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => Y p i) ^ 2) < ⊤ →
    ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c,
      ENNReal.ofReal (vnorm2 (fun i => lmUDer μ u Y p.1 p.2 i) ^ 2) < ⊤

/-- **`s ↦ w(s) ⟨χ, u(s)⟩` is integrable** for `u ∈ L²_loc((0,∞); L²(cell))` and `w` continuous with
compact support in `(0,∞)` (Fubini on `[a, b] × cell`, `|conj χ · u| ≤ |χ|² + |u|²`). -/
def LMIpWeightedInt : Prop :=
  ∀ (c : ℝ) (χ : LMSpField) (u : ℝ → LMSpField) (w : ℝ → ℝ), LMCellL2 c χ →
    (∀ i, Measurable fun p : ℝ × (ℝ × ℝ) => u p.1 p.2 i) →
    (∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ →
      ∫⁻ p in Icc s₁ s₂ ×ˢ B0579.cell c, ENNReal.ofReal (vnorm2 (fun i => u p.1 p.2 i) ^ 2) < ⊤) →
    Continuous w → HasCompactSupport w → tsupport w ⊆ Ioi (0 : ℝ) →
    Integrable (fun s => ((w s : ℝ) : ℂ) * LMIp c χ (u s)) (volume.restrict (Ioi (0 : ℝ)))

/-! ## The pairing identity on a good slice -/

/-- **`Re ⟨𝒫₀ Z, u_k⟩ = -(ν N_k + R_k)` on a good slice** (SP 3541-3552): `𝒫₀ u_k = u_k`,
`LMAntiSymm`, `∂ⱼ J_k u_k = J_k J_k G_{·j}` (`lmMoll_pd2_eq`), self-adjointness of `J_k` and
`∂ⱼ u_k = J_k G_{·j}` (`lmMoll_pd_eq`). -/
def LMPairingSlice : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ),
    FreeSolData c ν μ F b G → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J → LMMollH1 c J →
    ∀ (k : ℕ) (s : ℝ), 0 < s → LMGoodSlice c F G b s →
      (LMIp c (P0C c (lmDivJ J k (fun y => lmTens ν F G (s, y)))) (LMMollU J b k s)).re =
        -(ν * LMMollN c J b k s + LMMollR c J F b k s)

/-- **The tensor term of the tested equation** (SP 3427-3440): with `w = J_k 𝒫₀ χ`,
`∑ᵢⱼ ∫ conj(∂ⱼ wᵢ) Tᵢⱼ = -⟨χ, 𝒫₀ Z⟩` (`LMAntiSymm` columnwise, `LMP0CAdj`). -/
def LMSliceTensor : Prop :=
  ∀ c : ℝ, 0 < c → ∀ J : ℕ → LMSpField → LMSpField, IsLMMollifier c J → LMMollH1 c J →
    ∀ (k : ℕ) (χ : LMSpField) (T : ℝ × ℝ → Fin 2 → Fin 2 → ℂ), LMCellL2 c χ →
      (∀ j : Fin 2, LMCellL2 c (fun y i => T y i j)) →
      ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in B0579.cell c,
          starRingEnd ℂ (LMPd j (fun y => J k (P0C c χ) y i) x) * T x i j =
        -LMIp c χ (P0C c (lmDivJ J k T))

end UnforcedLeray.Short.IIIa
