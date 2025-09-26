package com.capsule

import android.app.Activity
import android.os.Bundle
import android.util.Log
import android.widget.TextView
import android.view.ViewGroup
import android.view.Gravity
import android.content.pm.PackageManager

class MainActivity : Activity() {
  private fun provenance(tag: String) {
    try {
      val pm = packageManager
      val p = pm.getPackageInfo(packageName, 0)
      Log.i("Capsule", "[$tag] pkg=$packageName code=${p.longVersionCode} name=${p.versionName} cls=${this::class.java.name}")
    } catch (e: PackageManager.NameNotFoundException) {
      Log.w("Capsule", "[$tag] package info lookup failed", e)
    }
  }

  override fun onCreate(savedInstanceState: Bundle?) {
    super.onCreate(savedInstanceState)
    provenance("onCreate")
    val tv = TextView(this).apply {
      text = "Capsule — witness zero"
      textSize = 20f
      gravity = Gravity.CENTER
      layoutParams = ViewGroup.LayoutParams(
        ViewGroup.LayoutParams.MATCH_PARENT,
        ViewGroup.LayoutParams.MATCH_PARENT
      )
    }
    setContentView(tv)
  }

  override fun onResume() {
    super.onResume()
    provenance("onResume")
  }
}
