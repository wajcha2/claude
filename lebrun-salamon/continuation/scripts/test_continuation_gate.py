#!/usr/bin/env python3
"""Focused continuation transition/corruption tests. No Lean/compiler execution."""
import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path
import continuation_support as c
from replay_checkpoint import runtime_context, source_ancestry_fingerprint
from run_continuation_audit import generate_audit
from verify_continuation_boundaries import parse_audit, reconcile
from finalize_continuation_evidence import check_completed_stages

FLAGS = ["--json", "-j1", "-DElab.async=false", "-M12000",
         "-DmaxErrors=1000", "-DmaxHeartbeats=2000000"]


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def manifest(root):
    rows = {p.relative_to(root).as_posix(): c.digest(p) for p in (root / "source").rglob("*.lean")}
    write(root / "SOURCE.sha256", "".join(rows[p] + "  " + p + "\n" for p in sorted(rows)))


class NativeFixture:
    def __init__(self, base):
        self.root, self.build, self.external = base / "root", base / "build", base / "external"
        write(self.external / "Mathlib.olean", "synthetic-external-output")
        for name, text in {"A":"import Mathlib\n-- A\n","B":"import A\n-- B\n",
                           "C":"import B\n-- C\n","D":"import Mathlib\n-- independent D\n"}.items():
            write(self.root / "source" / (name + ".lean"), text)
        write(self.root / "target/MainStatement.lean", "synthetic-frozen-target\n")
        write(self.root / "TOOLCHAIN.lock.json", '{"synthetic":true}\n')
        manifest(self.root)
        self.config = {"compiler_kind":"stock_pinned_frontend","flags":FLAGS,
                       "mathlib_revision":"test-only","external_olean_roots":[str(self.external)],
                       "fingerprint_files":[]}
        self.identity, self.fp = runtime_context(self.root, self.config)
        self.baseline = {"runtime_fingerprint":self.fp,"runtime_flags":FLAGS,"mathlib_revision":"test-only",
                         "target_sha256":c.digest(self.root/"target/MainStatement.lean"),
                         "lock_sha256":c.digest(self.root/"TOOLCHAIN.lock.json")}
        self.generate()

    def generate(self):
        inv, good, states = c.source_inventory(self.root), {}, {}
        for module in inv["order"]:
            deps = {}
            for dep in inv["imports"][module]:
                p = self.build/"olean"/(dep+".olean") if dep in good else self.external/(dep+".olean")
                deps[dep] = {"kind":"project" if dep in good else "external","sha256":c.digest(p)}
            key = {"source_sha256":c.digest(inv["sources"][module]),"imports":inv["imports"][module],
                   "dependency_artifacts":deps,"runtime_fingerprint":self.fp,"flags":FLAGS}
            output = self.build/"olean"/(module+".olean")
            write(output,"synthetic-identical-output-"+module)
            stdout,stderr = self.build/"logs"/(module+".jsonl"),self.build/"logs"/(module+".stderr")
            write(stdout,""); write(stderr,"")
            stamp = source_ancestry_fingerprint(module,key,
                {d:good[d]["source_ancestry_fingerprint"] for d in inv["graph"][module]})
            rec = {"schema":"lebrun-module-receipt-v1","module":module,"status":"passed","return_code":0,
                   "evidence_kind":"native_kernel_compilation","key":key,"output_sha256":c.digest(output),
                   "source_ancestry_fingerprint":stamp,"stdout":str(stdout),"stderr":str(stderr),
                   "stdout_sha256":c.digest(stdout),"stderr_sha256":c.digest(stderr),"seconds":0.1}
            c.write_json(self.build/"receipts"/(module+".json"),rec)
            good[module] = rec
            states[module] = {"status":"passed","output_sha256":rec["output_sha256"]}
        c.write_json(self.build/"RUN_STATUS.json",{"runtime":self.identity,"runtime_fingerprint":self.fp,
            "selected_modules":inv["order"],"modules":states,"final_validation":{
                "invalidated_modules":{},"changed_runtime_files":[],"checked_module_count":len(good)}})

    def verify(self):
        return c.verify_native_build(self.root,self.build,self.config,self.baseline)

    def edit_receipt(self,name,change):
        path=self.build/"receipts"/(name+".json"); rec=c.read_json(path)
        change(rec); c.write_json(path,rec)


class NativeIntegrityTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.f=NativeFixture(Path(self.tmp.name))

    def test_complete_strict_native_fixture(self):
        r=self.f.verify()
        self.assertTrue(r["whole_current_graph_passed"])
        self.assertEqual(r["accepted_modules"],4)

    def test_output_log_receipt_import_runtime_and_membership_corruption(self):
        mutations=[
            lambda:write(self.f.build/"olean/B.olean","altered"),
            lambda:write(self.f.build/"logs/B.jsonl","altered"),
            lambda:self.f.edit_receipt("B",lambda r:r.update(source_ancestry_fingerprint="0"*64)),
            lambda:self.f.edit_receipt("B",lambda r:r["key"].update(imports=[])),
            lambda:self.f.edit_receipt("B",lambda r:r.update(evidence_kind="local_diagnostic")),
            lambda:self.f.edit_receipt("B",lambda r:r.update(return_code=1)),
            lambda:self.f.config.update(flags=FLAGS+["-DmaxHeartbeats=0"]),
            lambda:write(self.f.root/"source/Unexpected.lean","import Mathlib\n"),
            lambda:write(self.f.root/"target/MainStatement.lean","changed target")]
        snapshot=Path(self.tmp.name)/"snapshot"; shutil.copytree(self.f.root,snapshot)
        config=copy.deepcopy(self.f.config)
        for i,mutate in enumerate(mutations):
            with self.subTest(corruption=i):
                shutil.rmtree(self.f.root); shutil.copytree(snapshot,self.f.root)
                self.f.config=copy.deepcopy(config); self.f.generate(); mutate()
                with self.assertRaises((c.GateError,KeyError,FileNotFoundError)):
                    self.f.verify()

    def test_stale_descendant_rejected_even_if_intermediate_olean_identical(self):
        old=self.f.verify(); stale=(self.f.build/"receipts/B.json").read_bytes()
        write(self.f.root/"source/A.lean","import Mathlib\n-- changed ancestor\n")
        manifest(self.f.root); self.f.generate(); current=self.f.verify()
        self.assertEqual(old["records"]["B"]["output_sha256"],current["records"]["B"]["output_sha256"])
        self.assertNotEqual(c.context_hash(old["records"]["B"]),c.context_hash(current["records"]["B"]))
        (self.f.build/"receipts/B.json").write_bytes(stale)
        with self.assertRaisesRegex(c.GateError,"Recursive ancestry"):self.f.verify()

    def test_failed_stage_is_not_pass_even_with_output(self):
        self.f.edit_receipt("C",lambda r:r.update(status="failed",return_code=1))
        path=self.f.build/"RUN_STATUS.json"; s=c.read_json(path)
        s["modules"]["C"]["status"]="failed"; s["final_validation"]["checked_module_count"]=3
        c.write_json(path,s); r=self.f.verify()
        self.assertFalse(r["full_selected_graph_passed"])
        self.assertFalse(r["whole_current_graph_passed"])
        self.assertEqual(r["errors"][0]["module"],"C")

    def test_exact_preservation_and_replacement_policy(self):
        old=self.f.verify()
        b={"native_contexts":{m:c.context_hash(r) for m,r in old["records"].items()}}
        change={"baseline_contexts_to_replace":["A","B","C"],"added_modules":[],
                "affected_current_modules":["A","B","C"]}
        with self.assertRaisesRegex(c.GateError,"retained its historical context"):c.compare_contexts(old,b,change)
        write(self.f.root/"source/A.lean","import Mathlib\n-- changed\n")
        manifest(self.f.root); self.f.generate()
        r=c.compare_contexts(self.f.verify(),b,change)
        self.assertEqual(r["preserved_baseline_contexts"],["D"])
        self.assertEqual(r["verified_replacement_contexts"],["A","B","C"])


class GraphPlanTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        base=Path(self.tmp.name); self.old,self.cur=base/"old",base/"current"
        generic="theorem generic : True := by sorry\n"
        before="import Mathlib\ntheorem target : True := by sorry\n"
        after="import Mathlib\n"+generic+"theorem target : True := by exact generic\n"
        self.leaf="theorem leaf : True := by sorry\n"
        write(self.old/"source/A.lean",before); write(self.old/"source/B.lean","import A\n"+self.leaf)
        manifest(self.old); shutil.copytree(self.old,self.cur)
        write(self.cur/"source/A.lean",after); write(self.cur/"source/H.lean","import Mathlib\n")
        manifest(self.cur); inv=c.source_inventory(self.old)
        self.b={"accepted_commit":"accepted","source_manifest_sha256":inv["sha256"],"source_manifest":inv["text"],
            "new_roots":[{"id":"OBL-044","module":"A","original_header":"theorem target : True"}],
            "point1_roots":[{"id":"OBL-001","module":"B"}],"point1_boundary_modules":["A","B"],
            "protected_files":{},"leaf_policies":[{"name":"leaf","module":"B",
            "policy":"unchanged_declaration_and_native_type_rebinding","declaration_source":self.leaf,
            "declaration_sha256":c.sha_text(self.leaf)}]}
        review={"schema":"lebrun-independent-publication-review-v1","reviewer":"root",
            "source":{"path":"source/A.lean","candidate_sha256":c.sha_text(after)},
            "interfaces":[{"declaration":"generic","declaration_sha256":c.sha_text(generic),"eligible":True,
                           "primary_sources":["https://example.invalid/primary-test-fixture"]}]}
        c.write_json(self.cur/"audit/review.json",review)
        self.plan={"schema":"lebrun-continuation-candidate-plan-v1","status":"approved_for_native_validation",
            "dispatch_authorized":True,"baseline_accepted_commit":"accepted",
            "baseline_source_manifest_sha256":inv["sha256"],"baseline_accepted_units":74,"denominator":133,
            "candidate_manifest_sha256":c.source_inventory(self.cur)["sha256"],
            "source_edits":[{"path":"source/A.lean","baseline_sha256":c.sha_text(before),
                            "candidate_sha256":c.sha_text(after),"patches":[{"before":before,"after":after}]}],
            "added_sources":[{"path":"source/H.lean","sha256":c.digest(self.cur/"source/H.lean")}],
            "publication_reviews":[{"path":"audit/review.json","sha256":c.digest(self.cur/"audit/review.json"),
                                   "declarations":[{"name":"generic","declaration_source":generic}]}]}

    def test_dynamic_added_module_and_reverse_cone(self):
        _,inv,change=c.candidate_plan(self.cur,self.old,self.b,self.plan)
        self.assertEqual(len(inv["sources"]),3)
        self.assertEqual(change["affected_current_modules"],["A","B","H"])
        self.assertEqual(change["baseline_contexts_to_replace"],["A","B"])
        self.assertEqual(change["reaudit_point1_root_ids"],["OBL-001"])

    def test_placeholder_plan_cannot_authorize_compile(self):
        p=copy.deepcopy(self.plan); p.update(status="awaiting_complete_candidate_handoff",dispatch_authorized=False)
        with self.assertRaisesRegex(c.GateError,"handoff and guard approval"):c.candidate_plan(self.cur,self.old,self.b,p)

    def test_bad_inverse_unapproved_edit_and_public_header_change_rejected(self):
        for kind in ("inverse","unapproved","header"):
            with self.subTest(kind=kind):
                p,b=copy.deepcopy(self.plan),copy.deepcopy(self.b)
                if kind=="inverse":p["source_edits"][0]["patches"][0]["before"]="absent"
                elif kind=="unapproved":p["source_edits"]=[]
                else:b["new_roots"][0]["original_header"]="different header"
                with self.assertRaises(c.GateError):c.candidate_plan(self.cur,self.old,b,p)

    def test_unchanged_published_leaf_body_is_required(self):
        after="import A\ntheorem leaf : True := by trivial\n"
        write(self.cur/"source/B.lean",after); manifest(self.cur)
        p=copy.deepcopy(self.plan); p["candidate_manifest_sha256"]=c.source_inventory(self.cur)["sha256"]
        before=(self.old/"source/B.lean").read_text()
        p["source_edits"].append({"path":"source/B.lean","baseline_sha256":c.sha_text(before),
            "candidate_sha256":c.sha_text(after),"patches":[{"before":before,"after":after}]})
        with self.assertRaisesRegex(c.GateError,"Published declaration was changed"):c.candidate_plan(self.cur,self.old,self.b,p)

    def test_retired_original_body_may_change_with_exact_header(self):
        self.b["leaf_policies"].append({"name":"target","module":"A",
            "policy":"retire_direct_admission_preserve_header_and_native_type"})
        c.candidate_plan(self.cur,self.old,self.b,self.plan)

    def test_stale_independent_review_rejected(self):
        p=copy.deepcopy(self.plan); p["publication_reviews"][0]["sha256"]="0"*64
        with self.assertRaisesRegex(c.GateError,"review bytes changed"):c.candidate_plan(self.cur,self.old,self.b,p)

    def test_missing_independent_reviewer_rejected(self):
        path=self.cur/"audit/review.json"; review=c.read_json(path)
        del review["reviewer"]; c.write_json(path,review)
        p=copy.deepcopy(self.plan); p["publication_reviews"][0]["sha256"]=c.digest(path)
        with self.assertRaisesRegex(c.GateError,"Unapproved publication review"):
            c.candidate_plan(self.cur,self.old,self.b,p)


class BoundaryTests(unittest.TestCase):
    def fixtures(self):
        def sig(n,m="A",typ="True"):
            return {"name":n,"module":m,"level_params":"","native_type":typ,"native_type_sha256":c.sha_text(typ)}
        def rec(m):
            return {"key":{"source":m},"output_sha256":"o"+m,"stdout_sha256":"s"+m,
                    "stderr_sha256":"e"+m,"source_ancestry_fingerprint":"a"+m}
        native={"records":{m:rec(m) for m in ["A","D"]}}
        b={"point1_roots":[{"id":"OBL-001","declaration":"P","module":"D","direct_leaves":[]},
                            {"id":"OBL-002","declaration":"R","module":"A","direct_leaves":["L"]}],
           "new_roots":[{"id":"OBL-044","declaration":"N","module":"A"}],
           "old_admitted_leaves":[{"name":"N","module":"A","source_sha256":"old"},
                                  {"name":"L","module":"A","source_sha256":"old"}],
           "leaf_policies":[{"name":"N","policy":"retire_direct_admission_preserve_header_and_native_type"},
                            {"name":"L","policy":"unchanged_declaration_and_native_type_rebinding"}],
           "native_contexts":{"D":c.context_hash(native["records"]["D"])},
           "historical_signature_scope":{"native":15,"lexical":29},"accepted_units":74}
        change={"preserved_point1_root_ids":["OBL-001"],"reaudit_point1_root_ids":["OBL-002"],"new_root_ids":["OBL-044"]}
        old={"signatures":{n:sig(n,"D" if n=="P" else "A") for n in ["P","R","N","L"]},"evidence":{}}
        current=copy.deepcopy(old); current["signatures"]["G"]=sig("G"); current["roots"]={}
        for n,i in [("R","OBL-002"),("N","OBL-044")]:
            current["roots"][n]={"id":i,"declaration":n,"leaves":{
                "G":{"name":"G","module":"A","native_type":"True","native_type_sha256":c.sha_text("True")}}}
        return b,change,old,current,native,{"G":{"name":"G","module":"A","source_sha256":"new"}},\
            {"files":{"source/A.lean":"new","source/D.lean":"oldD"}}

    def test_complete_accounting_retires_original_without_credit(self):
        r=reconcile(*self.fixtures())
        self.assertEqual(r["original_root_accounting_count"],3)
        self.assertEqual(r["fresh_current_native_root_audits"],2)
        self.assertEqual(r["preserved_historical_root_boundaries"],1)
        self.assertNotIn("N",r["eligible_leaf_bindings"])
        self.assertEqual(r["accepted_units_unchanged"],74)

    def test_retired_original_or_unreviewed_admission_rejected(self):
        for name in ["N","R","Unreviewed"]:
            f=list(self.fixtures()); f[3]["roots"]["R"]["leaves"][name]={"name":name,"module":"A","native_type":"True"}
            with self.subTest(name=name),self.assertRaises(c.GateError):reconcile(*f)

    def test_native_type_universe_or_missing_root_rejected(self):
        for kind in ["type","universe","missing"]:
            f=list(self.fixtures())
            if kind=="type":f[3]["signatures"]["N"]["native_type"]="False"
            elif kind=="universe":f[3]["signatures"]["N"]["level_params"]="u"
            else:del f[3]["roots"]["N"]
            with self.subTest(kind=kind),self.assertRaises(c.GateError):reconcile(*f)

    def test_preserved_root_requires_exact_native_context(self):
        f=list(self.fixtures()); f[4]["records"]["D"]["source_ancestry_fingerprint"]="changed"
        with self.assertRaisesRegex(c.GateError,"changed native context"):reconcile(*f)

    def test_complete_parser_and_corruption_cases(self):
        spec={"signatures":{"R":"A"},"walks":[{"declaration":"R","id":"OBL-001"}]}
        messages=["CI_SIGNATURE R\nLEVEL_PARAMS \nMODULE A\nTYPE True","CI_SIGNATURES_COMPLETE",
                  "CI_ROOT OBL-001 R",
                  "CI_SUMMARY root=R all_constants=2 project_constants=1 direct_sorry_count=0 missing_count=0 custom_project_axiom_count=0 nonstandard_axiom_count=0",
                  "CI_BOUNDARIES_COMPLETE","'R' does not depend on any axioms."]
        def logs(ms):return "\n".join(json.dumps({"severity":"information","data":m}) for m in ms)
        self.assertEqual(len(parse_audit(logs(messages),spec)["roots"]),1)
        for bad in [messages[:-1],messages+[messages[0]],[m.replace("TYPE True","TYPE ⋯") for m in messages],
                    [m for m in messages if not m.startswith("CI_SUMMARY")]]:
            with self.assertRaises(c.GateError):parse_audit(logs(bad),spec)
        real=messages[:-1]+["'R' depends on axioms: [propext,\n sorryAx.{u},\n Classical.choice.{u},\n Quot.sound.{u}]"]
        self.assertEqual(parse_audit(logs(real),spec)["roots"]["R"]["all_module_axioms"],
                         ["Classical.choice","Quot.sound","propext","sorryAx"])
        bad=messages[:-1]+["'R' depends on axioms: [propext, Unreviewed.axiom.{u, v}]"]
        with self.assertRaises(c.GateError):parse_audit(logs(bad),spec)

    def test_generator_module_names_are_data_and_explicit_type_options(self):
        spec={"mode":"current","signatures":{"A.realTheorem":"A"},
              "walks":[{"declaration":"A.realTheorem","id":"OBL-001"}],"imports":["A"]}
        text=generate_audit(spec,["ModuleWithNoDeclaration"])
        self.assertIn('Array String := #["ModuleWithNoDeclaration"]',text)
        self.assertNotIn(chr(96)*2+"ModuleWithNoDeclaration",text)
        self.assertIn("set_option pp.all true",text)
        self.assertNotIn("pp.width",text)


class FinalStageTests(unittest.TestCase):
    def test_failed_missing_stale_or_count_corruption_cannot_pass_final_gate(self):
        rec={"key":{},"output_sha256":"o","stdout_sha256":"s","stderr_sha256":"e","source_ancestry_fingerprint":"a"}
        native={"records":{"A":rec},"source_manifest_sha256":"m","whole_current_graph_passed":True,"errors":[]}
        pre={"stages":{n:{"selected":["A"],"module_timeout_seconds":300} for n in ["core","full"]}}
        stages={n:{"stage":n,"return_code":0,"full_selected_graph_passed":True,"errors":[],
            "source_manifest_sha256":"m","candidate_plan_sha256":"p","baseline_record_sha256":"b",
            "selected":["A"],"records":{"A":rec},"module_timeout_seconds":300,
            "fresh_native_passes_this_invocation":1,"native_receipts_reused_this_invocation":0,
            "whole_current_graph_passed":True} for n in pre["stages"]}
        check_completed_stages(pre,stages,native,"p","b")
        for kind in ["missing","failed","false_full","stale","wrong_count"]:
            s=copy.deepcopy(stages)
            if kind=="missing":del s["core"]
            elif kind=="failed":s["core"]["return_code"]=1
            elif kind=="false_full":s["full"]["whole_current_graph_passed"]=False
            elif kind=="stale":s["core"]["records"]["A"]["source_ancestry_fingerprint"]="old"
            else:s["full"]["native_receipts_reused_this_invocation"]=1
            with self.subTest(kind=kind),self.assertRaises(c.GateError):check_completed_stages(pre,s,native,"p","b")


if __name__=="__main__":
    unittest.main(verbosity=2)

