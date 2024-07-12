# Python imports
import time

# Local imports
from Erebor import Erebor
from SQISign import specialSQISign_strong, specialSQISign
from utilities import print_info

N = 3
full_anon = True
if full_anon:
    ring_users = [ specialSQISign_strong() for _ in range(N)] 
else:
    ring_users = [ specialSQISign() for _ in range(N)] 
ring_pk = []

for us in ring_users:
    us.keygen()
    ring_pk.append(us.export_public_key())

idx = randint(0,2)
user = ring_users[idx]

RS = Erebor(ring_pk, user)


msg = b"la risposta, 42"

sig = RS.sign(msg)

print_info('Starting Signing')

print(sig[0])
print(sig[1])

print_info('Starting Verification')

Rverifier = Erebor(ring_pk, user = None, full_anon = full_anon)

if Rverifier.verify(sig, msg):
    print('Verification Succeeded, hooray!')
else:
    print('Verification Failed')

