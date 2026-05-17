/- Examples-level aggregate for examples/AllTests.v.

The upstream file is a QuickChick test driver. In this Lean port the runnable
test harness is `Tests.lean`; this module keeps an examples-level aggregate of
the ported executable test modules. -/

import ConCert.Examples.BAT.BATAltFixTests
import ConCert.Examples.BAT.BATFixedTests
import ConCert.Examples.BAT.BATTests
import ConCert.Examples.BoardroomVoting.BoardroomVotingTest
import ConCert.Examples.Congress.CongressTests
import ConCert.Examples.Congress.Congress_BuggyTests
import ConCert.Examples.Dexter.DexterTests
import ConCert.Examples.Dexter2.Dexter2Tests
import ConCert.Examples.EIP20.EIP20TokenTests
import ConCert.Examples.Escrow.EscrowTests
import ConCert.Examples.ExchangeBuggy.ExchangeBuggyTests
import ConCert.Examples.FA2.FA2TokenTests
import ConCert.Examples.ITokenBuggy.ITokenBuggyTests
