package main

import (
	"fmt"
)

// UserService handles user-related operations
type UserService struct {
	users map[string]*User
}

// User represents a user in the system
type User struct {
	ID    string `json:"id"`
	Name  string `json:"name"`
	Email string `json:"email"`
}

// CreateUser creates a new user
func (us *UserService) CreateUser(name, email string) (*User, error) {
	if name == "" {
		return nil, fmt.Errorf("name cannot be empty")
	}
	
	user := &User{
		ID:    generateID(us.users),
		Name:  name,
		Email: email,
	}
	
	us.users[user.ID] = user
	return user, nil
}

// GetUser retrieves a user by ID
func (us *UserService) GetUser(id string) (*User, error) {
	user, exists := us.users[id]
	if !exists {
		return nil, fmt.Errorf("user with ID %s not found", id)
	}
	return user, nil
}

func generateID(users map[string]*User) string {
	// Simple ID generation for demo
	return fmt.Sprintf("user_%d", len(users))
}
