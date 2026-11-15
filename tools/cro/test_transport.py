import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from cro import make
from transport import derive, window


class TransportTests(unittest.TestCase):
    def setUp(self):
        self.path = Path("fixtures/periodic-ode.cycle.json")
        self.data = json.loads(self.path.read_text())

    def test_order_two_and_subdivision(self):
        result = derive(self.data)
        self.assertEqual(result["monodromy"], [[1, 4], [0, 1]])
        self.assertEqual(result["translation"], [2, 0])
        receipt = make(result["complex"])
        self.assertEqual(receipt["order"], 2)
        joined = {**self.data, "windows": [{**self.data["windows"][0], "duration": 1}]}
        self.assertEqual(derive(joined)["complex"], result["complex"])

    def test_nonzero_second_order_forcing(self):
        linear, inverse, shift = window({"duration": 1, "N": [[0, 2], [0, 0]],
                                         "forcing": [0, 1]}, 2)
        self.assertEqual((linear, inverse, shift), ([[1, 2], [0, 1]], [[1, -2], [0, 1]], [1, 1]))

    def test_noncommuting_windows(self):
        first = {"duration": 1, "N": [[0, 1], [0, 0]], "forcing": [1, 0]}
        second = {"duration": 1, "N": [[0, 0], [2, 0]], "forcing": [0, 1]}
        result = derive({**self.data, "windows": [first, second]})
        self.assertEqual(result["monodromy"], [[1, 1], [2, 3]])
        self.assertEqual(result["translation"], [1, 3])

    def test_invalid_window(self):
        for changes in [{"duration": "1/3"}, {"duration": 0}, {"duration": 0.5},
                        {"N": [[1, 0], [0, 1]]}, {"forcing": [0, 1]}]:
            data = copy.deepcopy(self.data)
            data["windows"][0].update(changes)
            with self.assertRaises(ValueError, msg=changes):
                derive(data)

    def test_cli_replays_and_rejects_tampering(self):
        bundle = Path("fixtures/periodic-ode.bundle.json")
        command = [sys.executable, "-S", "transport.py", "verify", str(self.path)]
        checked = subprocess.run([*command, str(bundle)], capture_output=True)
        self.assertEqual(checked.returncode, 0, checked.stderr)
        for mutate in [lambda x: x.update(translation=[0, 0]),
                       lambda x: x.update(translation=[2.0, 0]),
                       lambda x: x["receipt"].update(order=4),
                       lambda x: x.update(cycle_sha256="0" * 64)]:
            record = json.loads(bundle.read_text())
            mutate(record)
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "mutated.json"
                path.write_text(json.dumps(record))
                self.assertNotEqual(subprocess.run([*command, str(path)], capture_output=True).returncode, 0)
