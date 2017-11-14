from fabric.api import run
from fabric.api import sudo
from fabric.api import cd
from fabric.api import env
from fabric.operations import put

env.host_string    = "eeehandel"
env.use_ssh_config = True
env.output_prefix  = False

def gen():
    with cd("sync_verif"):
        put("gates/gates.v", "gates/gates.v")
        put("generated/*", "generated")

def verif():
    with cd("sync_verif"):
        run("source ./setup && ./go.sh")
