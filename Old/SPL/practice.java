public class Foo {
  public static void main (String parameter, Locker locker) {
    int lockId = locker.lock();
    try {
      int i = parameter.length();
      firstOperation(i);
      log("..." + i);
      secondOperation(i);
    } finally {
      locker.unlock(lockId);
    }
  }
}

public class Foo {
  public static void main (String parameter, Locker locker) {
      int i = parameter.length();
      firstOperation(i);
    }
  }
}

Aspect lockAspect {
  declare precedence : 1;
  Locker locker;
  int lockId;
  before() : call(void Foo.main(String, Locker)) {
    this.lockId = locker.lock();
    this.locker = locker;
  }
  after() : call(void Foo.main(..)) {
    locker.unlock(lockId);
  }
}

Aspect LogAspect {
  after(int i) : call(* firstOperation(int)) && args(i) {
    log("..." + i);
  }
}

Aspect tryAspect {
  declare precedence : 0;
  
  around(String parameter, Locker locker) : call(void Foo.main(String, Locker)) && args(parameter, locker) {
    try {
      proceed(parameter, locker);
    } finally {
    }
  }
}

Aspect secondAspect {

  11 secondOperation(i);
}

