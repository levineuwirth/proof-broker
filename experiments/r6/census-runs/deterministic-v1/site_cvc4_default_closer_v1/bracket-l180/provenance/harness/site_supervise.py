"""R6-011 site supervisor: register the verified census sites in this process, then run the frozen supervisor unchanged."""
import sys

import site_task
import supervise

if __name__ == '__main__':
    site_task.register_primary()
    sys.exit(supervise.main(sys.argv[1]))
