package com.face.secure.repositories;

import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

import com.face.secure.model.UserModel;

/**
 * Simplified in-memory repository implementation
 */
public class UserRepository {
    private final Map<Long, UserModel> users = new ConcurrentHashMap<>();
    private final AtomicLong idSequence = new AtomicLong(1);

    public UserModel save(UserModel user) {
        if (user.getId() == 0) {
            user.setId(idSequence.getAndIncrement());
        }
        users.put(user.getId(), user);
        return user;
    }

    public Optional<UserModel> findByLabel(int label) {
        return users.values().stream()
                .filter(user -> user.getLabel() == label)
                .findFirst();
    }
}
