package com.capsule

import android.app.Activity
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.util.Log
import java.io.File

class MainActivity : Activity() {

  private fun writeFile(dir: File, name: String, text: String) {
    try {
      if (!dir.exists()) dir.mkdirs()
      File(dir, name).writeText(text)
      Log.i("ZipFlow", "WROTE: " + name + " -> " + dir.absolutePath)
    } catch (t: Throwable) {
      Log.e("ZipFlow", "FAILED: " + name + " -> " + (t.message ?: "?"), t)
    }
  }

  override fun onCreate(savedInstanceState: Bundle?) {
    super.onCreate(savedInstanceState)
    val box = File(getExternalFilesDir("capsule_user"), "")
    val pkg = applicationContext.packageName
    writeFile(box, "hello.txt", "hello from " + pkg + "\n")
    writeFile(box, "boot.txt", "boot ok\n")
  }

  override fun onResume() {
    super.onResume()
    val box = File(getExternalFilesDir("capsule_user"), "")
    Handler(Looper.getMainLooper()).postDelayed({
      writeFile(box, "hello2.txt", "hello2 from resume\n")
      writeFile(box, "keep.txt", "keep\n")
    }, 1200)
  }
}
