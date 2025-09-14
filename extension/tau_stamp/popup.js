async function fetchReceipt() {
  try {
    const repo = "https://raw.githubusercontent.com/towre676-cloud/tau_crystal/main";
    const resp = await fetch(`${repo}/.tau_ledger/receipts/`);
    const text = await resp.text();
    const files = text.match(/href="([^"]+\.json)"/g)?.map(f => f.match(/href="(.+\.json)"/)[1]) || [];
    const latest = files.sort().pop();
    if (!latest) throw new Error("No receipts found");
    const receiptResp = await fetch(`${repo}/.tau_ledger/receipts/${latest}`);
    const receipt = await receiptResp.json();
    document.getElementById("receipt").textContent = latest;
    return { file: latest, sha256: receipt.wrapper_digest || "unknown" };
  } catch (e) { document.getElementById("status").textContent = `Error: ${e.message}`; document.getElementById("status").classList.add("error"); throw e; }
}
async function stampManifest() {
  try {
    const receipt = await fetchReceipt();
    const manResp = await fetch("https://raw.githubusercontent.com/towre676-cloud/tau_crystal/main/docs/manifest.md");
    const manifest = await manResp.text();
    const lines = manifest.split("\n");
    const newLines = [];
    let inSection = false;
    for (const line of lines) {
      if (line.startsWith("## tau_stamp (v1)")) { inSection = true; newLines.push(line, "", `receipt: ${receipt.file}`, `sha256: ${receipt.sha256}`, ""); }
      else if (inSection && line.startsWith("## ")) inSection = false;
      if (!inSection) newLines.push(line);
    }
    document.getElementById("hash").textContent = receipt.sha256;
    document.getElementById("status").textContent = "Stamped manifest with " + receipt.file;
  } catch (e) { document.getElementById("status").textContent = `Error: ${e.message}`; document.getElementById("status").classList.add("error"); }
}
document.getElementById("stamp").addEventListener("click", stampManifest);
fetchReceipt();
