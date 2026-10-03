/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/

/- Compatibility wrapper: reuse the already pinned, checked Quantum implementation
rather than defining a second copy of its global declarations. Normalized source
differences are recorded in port-logs/*.shared-diff.txt. -/

import Quantum.TraceInequality.LiebAndoTrace
