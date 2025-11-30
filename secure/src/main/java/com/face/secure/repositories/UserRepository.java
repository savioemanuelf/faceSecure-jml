package com.face.secure.repositories;

import java.util.HashMap;
import java.util.Map;
import com.face.secure.model.UserModel;

public class UserRepository {
    
    private final Map<Long, UserModel> users = new HashMap<>();
    private long idSequence = 1;

    public UserRepository() {}

    /*@ requires user != null;
      @ ensures \result == user;
      @*/
    //@ skipesc
    public UserModel save(UserModel user) {
        if (user.getId() == 0) {
            user.setId(idSequence++);
        }
        users.put(user.getId(), user);
        return user;
    }

    /*@ pure @*/
    //@ skipesc
    public /*@ nullable @*/ UserModel findByLabel(int label) {
        for (UserModel user : users.values()) {
            if (user.getLabel() == label) {
                return user;
            }
        }
        return null;
    }
}