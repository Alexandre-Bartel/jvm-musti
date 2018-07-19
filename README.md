# Musti

This is Musti, a modified JVM which checks at runtime that objects are properly initialized.
It prevents uninitialized object vulnerabilities from being exploited. A recent example of an 
uninitialized vulnerability is [CVE-2017-3289](https://access.redhat.com/security/cve/cve-2017-3289) which allows to completely bypass the JVM sandbox.
