import bugzilla, datetime, os, re, sys
from bugzilla._cli import DEFAULT_BZ

CVSS_PATTERN = re.compile(r"CVSSv3.1:SUSE:CVE-[0-9]{4}-[0-9]{4,}:([0-9].[0-9])")

def handle_email(email):
    if email == '__empty-env-var__':
        print("Please set the environment variable BUGZILLA_ACCOUNT_EMAIL to your bugzilla email or provide it after --email (-e).", file=sys.stderr)
        sys.exit(1)
    if len(email) < 9 or "@suse." not in email:
        print("no valid bz email provided", file=sys.stderr)
        sys.exit(1)
    return email

def get_score(s):
    m = re.search(CVSS_PATTERN, s)
    return m.group(1) if m else ''

def get_bugzilla_api():
    return bugzilla.Bugzilla(DEFAULT_BZ)

def check_being_logged_in(bzapi):
    if not bzapi.logged_in:
        print("You are not logged in the bugzilla!\n\nGo to https://bugzilla.suse.com/, log in via web interace with your credentials.\n"\
             "Then go to Preferences, click on the tab API KEYS and generate a new api key\nif you don't have one already.  Then store "\
             "the api_key in a file ~/.bugzillarc\nin the following format...\n\n# ~/.bugzillarc\n[apibugzilla.suse.com]\napi_key = YOUR_API_KEY")
        return False
    return True

def make_unique(alist):
    try:
        return { c for c in alist if c.startswith('CVE-') }.pop()
    except:
        return ''

def make_url(bug_id):
    return f'https://bugzilla.suse.com/show_bug.cgi?id={bug_id}'

def format_time(t):
    return datetime.datetime.strptime(str(t), '%Y%m%dT%H:%M:%S')

def get_backport_string(references, h, comment):
    return f'./scripts/git_sort/series_insert.py patches.suse/$(exportpatch -w -s -d patches.suse {" ".join(f"-F {r}" for r in references)} {h}) # {comment}'

def create_cache_dir(program_dir):
    cache_dir = os.getenv('XDG_CACHE_HOME', None)
    if not cache_dir:
        cache_dir = os.getenv('HOME', None)
        if not cache_dir:
            sys.exit(2)
        cache_dir = cache_dir + os.sep + '.cache'
    if not os.path.isdir(cache_dir):
        os.mkdir(cache_dir)
    if not os.path.isdir(cache_dir):
        sys.exit(3)
    program_dir = cache_dir + os.sep + program_dir
    if not os.path.isdir(program_dir):
        os.mkdir(program_dir)
    if not os.path.isdir(program_dir):
        sys.exit(4)
    return program_dir
