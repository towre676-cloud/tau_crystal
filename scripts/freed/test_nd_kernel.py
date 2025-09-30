import sys, os
from nd_kernel import selftest_emit_manifest
def main():
    mu=1.1
    os.makedirs("analysis/freed", exist_ok=True)
    os.makedirs(".tau_ledger/freed", exist_ok=True)
    mp=selftest_emit_manifest(mu, "analysis/freed", ".tau_ledger/freed")
    print("[manifest]", mp)
if __name__=="__main__": main()
