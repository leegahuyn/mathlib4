"""Trigger-only marker for the latest bounded Mock2 Advanced materialization run.

This file is deliberately not executed by the repair driver.  It exists only
so that the path-filtered verification workflow starts from the latest PR head
after the final CI/finalizer infrastructure was staged.  The final green-only
cleanup removes all temporary repair markers.
"""
