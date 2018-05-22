import React from 'react'

import profilePic from './profile-pic.jpg'

export default function Bio() {
  return (
    <div
      style={{
        display: 'flex',
      }}
    >
      <img
        src={profilePic}
        alt="Joel Burget"
        style={{
          marginBottom: 0,
          width: "100px",
          height: "100px",
        }}
      />
      <p>
        <strong>Joel Burget</strong>, cofounder{' '}
      </p>
    </div>
  )
}
