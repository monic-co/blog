import React from 'react'

import profilePic from './profile-pic.jpg'

export default function Bio() {
  return (
    <div
      style={{ display: 'flex' }}
    >
      <img
        src={profilePic}
        alt="Joel Burget"
        style={{
          marginBottom: 0,
          width: "100px",
          height: "100px",
          borderRadius: "50%",
        }}
      />
      <p
        style={{
          display: 'flex',
          flexDirection: 'column',
          justifyContent: 'center',
          marginLeft: 25,
        }}
      >
        <strong><a href="https://www.monic.co/about/">Joel Burget</a></strong>
        cofounder{' '}
      </p>
    </div>
  )
}
