from random import sample
from string import lowercase
from fabric.api import run
from fabric.api import sudo
from fabric.api import cd
from fabric.api import env
from fabric.state import output
from fabric.operations import put
from fabric.operations import get
from fabric.contrib.files import exists


project_name       = "sync-models"
workspace_dir      = "workspaces"
output["status"]   = False
output["running"]  = False
env.output_prefix  = False
env.use_ssh_config = True
versify_host       = "vmach"
ifv_host           = "eeebrahms"


def vers():
    env.host_string = versify_host

    put("examples/flat-arbiter/correct.blif", "/home/ubuntu/circuit.blif")
    put("examples/flat-arbiter/spec.g", "/home/ubuntu/spec.g")
    put("libraries/workcraft.lib", "/home/ubuntu/versify.genlib")
    put("libraries/extra.lib", "/home/ubuntu/extra.genlib")

    with cd("/home/ubuntu"):
        run("time versify -nosemi -Lversify.genlib -Ccircuit.blif -Espec.g")


def verify():

    env.host_string = ifv_host
    clean()

    run_name = "".join(sample(lowercase, 6))
    work_dir = "%s/%s/%s" % (workspace_dir, project_name, run_name)
    run("mkdir -p %s" % work_dir)

    with cd(work_dir):

        # Create project subdirectories
        run("mkdir -p workspace")
        run("mkdir -p generated")
        run("mkdir -p gates")

        # Copy files
        put("gates/*", "gates")
        put("generated-ifv-perf/*", "generated")
        put("ifv/go.sh", "go.sh", mirror_local_mode=True)
        put("ifv/run.tcl", "run.tcl")

        # Run ifv
        run("module load cadence-license && ./go.sh")

        # Grab counter-example
        if exists("examples/counter.vcd"):
            get("examples/counter.vcd", "counter.vcd")


def clean():

    env.host_string = ifv_host
    work_dir = "%s/%s/" % (workspace_dir, project_name)
    run("rm -rf %s" % work_dir)
