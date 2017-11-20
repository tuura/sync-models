from random import sample
from string import lowercase
from fabric.api import run
from fabric.api import sudo
from fabric.api import cd
from fabric.api import env
from fabric.state import output
from fabric.operations import put
from fabric.operations import get


project_name       = "sync-models"
workspace_dir      = "workspaces"
env.host_string    = "eeehandel"
output["status"]   = False
output["running"]  = False
env.output_prefix  = False
env.use_ssh_config = True


def verify():

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
        put("generated/*", "generated")
        put("ifv/go.sh", "go.sh", mirror_local_mode=True)
        put("ifv/run.tcl", "run.tcl")

        # Run ifv
        run("module load cadence-license && ./go.sh")

        get("examples/counter.vcd", "counter.vcd")


def clean():
    work_dir = "%s/%s/" % (workspace_dir, project_name)
    run("rm -rf %s" % work_dir)
