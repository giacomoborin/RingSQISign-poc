"""
Similar to how `example_SQISign.sage is written, but with more
assertions and debugging prints. 
"""

# Python imports
import time

# Local imports
from code.SQISign import specialSQISign
from code.utilities import print_info
from code.setup import *

prover = specialSQISign()
verifier = specialSQISign()

print_info("Starting SQISign")
sqisign_time = time.time()

# Keygen
print_info("Starting Keygen")
keygen_time = time.time()
prover.keygen()
print_info(f"Keygen took {time.time() - keygen_time:5f}")

# Unpack and check keygen
Epk = prover.pk
Iτ, τ, τ_ker = prover.sk
assert gcd(Dc, T_prime) == 1
assert Iτ.norm() == T_prime
assert τ_ker.order() == T_prime
assert τ.degree() == T_prime

# Commitment
print_info("Starting Commitment")
commitment_time = time.time()
Ecmt = prover.commitment()
print_info(f"Commitment took {time.time() - commitment_time:5f}")

# Check commitment secret values
psi_prime, Ipsi, Jpsi = prover.commitment_secrets
assert psi_prime.degree() == Jpsi.norm()

# Challenge
print_info("Starting Challenge")
challenge_time = time.time()
ϕ_ker = verifier.challenge(Epk = Epk, Ecmt = Ecmt)
print_info(f"Challenge took {time.time() - challenge_time:5f}")

# Check Challenge
assert ϕ_ker.order() == Dc
assert ϕ_ker in Epk

# Response
print_info("Starting Response")
response_time = time.time()
S = prover.response(ϕ_ker)
print_info(f"Response took {time.time() - response_time:5f}")

# Verification
print_info("Starting Verification")
verify_time = time.time()
EA = prover.export_public_key()
response_valid = verifier.verify_response(Epk, S, ϕ_ker)

# Check verification
print_info(f"Verification took {time.time() - verify_time:5f}")
assert response_valid, "SQISign response was not valid"
print(f"INFO [SQISign]: SQISign was successful!")

# All finished!
print_info(f"SQISign took {time.time() - sqisign_time:5f}")
