/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FredholmAlternative.Basic
public import TauCeti.Analysis.PDE.FredholmAlternative.Coefficients

/-!
# The Fredholm alternative for weak Dirichlet problems

This module preserves the public `TauCeti.Analysis.PDE.FredholmAlternative` import while the
implementation is split between the abstract mass-shift reduction and its coefficient-level
instantiation.
-/
